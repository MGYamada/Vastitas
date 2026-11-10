# Numerical maps, GEMM, metrics and tensor networks

[Storage and resource programs](storage.md) gives a program buffers and
loans. This chapter gives a buffer a mathematical meaning: its cells are the
matrix of a linear map between two spaces, in a named basis of each. The
compiler can then check that a product of two matrices is the composite of
two maps, before the executable multiplies them.

Every statement of this chapter is a statement of a resource function.
`vastitas check` checks them without a numerical library.
[Building a numerical program](#building-a-numerical-program) says what
`vastitas build` needs.

## Coefficient profiles

A space is a space over the real or over the complex numbers. A program says
which with [indexed declarations](indexed-profile.md). The examples of this
chapter keep these declarations in a module `profiles`:

```vast
{{#include ../../examples/packages/numerical/src/profiles/mod.vast}}
```

The first group has these declarations:

- Two markers name the coefficients.
- `SmoothScalar` is a [*scalar base*](../appendix/glossary.md#scalar-base):
  the base of the smooth setting with real coefficients. `SmoothBase` is one
  object of it.
- `RealSmooth` and `ComplexSmooth` are
  [*linear implementations*](../appendix/glossary.md#linear-implementation)
  over that base. A space of `RealSmooth` stores cells of `F64`, and a space
  of `ComplexSmooth` stores cells of `Complex<F64>`.

The two other groups declare a real and a complex linear implementation over
bases of the scheme setting. Such a set of declarations is a
[*coefficient profile*](../appendix/glossary.md#profile). It creates no space
and no storage, and it states no law of arithmetic: the cells hold binary64
numbers, which approximate real and complex numbers.

## Spaces, bases and maps

The function `product` of
[`examples/packages/numerical`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/numerical)
multiplies a matrix with 2 rows and 3 columns by a matrix with 3 rows and 2
columns. It begins with three spaces and a basis of each:

```vast
{{#include ../../examples/packages/numerical/src/real/mod.vast:spaces}}
```

- `space u = linear(L, 2);` declares a
  [*space*](../appendix/glossary.md#space) of dimension 2 of the linear
  implementation `L`. Every `space` statement declares a different space:
  `u` and `w` have one implementation and one dimension, and they are two
  spaces.
- `basis bu = basis(u);` declares a [*basis*](../appendix/glossary.md#basis)
  of `u`. A basis holds no vectors. It is the name by which a map says what
  its coordinates mean.

The function then allocates three buffers and writes the two matrices:

```vast
{{#include ../../examples/packages/numerical/src/real/mod.vast:storage}}
```

The payloads are the bits of the numbers 1 to 12. The buffer `a` holds the
matrix with the rows (1, 2, 3) and (4, 5, 6). The buffer `b` holds the matrix
with the rows (7, 8), (9, 10) and (11, 12).

A [*map*](../appendix/glossary.md#numerical-map) presents a loan as the
matrix of a linear map:

```vast
{{#include ../../examples/packages/numerical/src/real/mod.vast:product}}
```

`map left = view(input_a, bv, bw);` presents the loan `input_a` as the matrix
of a map from the space of `bv` to the space of `bw`, in these two bases. The
matrix has one row for each dimension of the target space and one column for
each dimension of the source space. The statement copies nothing and reads no
cell.

## Multiplying maps

The last statement of that fragment,
`gemm(left, right, destination, overwrite, NativeFast);`, multiplies two
maps. It has the name of GEMM, the routine for a general matrix product in
the BLAS libraries. Here `right` is a map from `u` to `v`, `left` is a map
from `v` to `w`, and `destination` is a map from `u` to `w`. The statement
writes to `destination` the matrix of `left` after `right`.

The compiler accepts the statement only when the three maps fit. The source
basis of `left` must be the target basis of `right`, and `destination` must
lead from the source basis of `right` to the target basis of `left`. The
statement conjugates nothing and transposes nothing.

With `overwrite` the statement ignores the old cells of the output, so
`output` may be a `write` loan of cells that hold no value. `NativeFast`
names the numerical policy: the executable computes the product with a
native routine in binary64 arithmetic. The result is not a product of real
numbers.

The function checks the product and then adds a second product to it:

```vast
{{#include ../../examples/packages/numerical/src/real/mod.vast:accumulate}}
```

The product is the matrix with the rows (58, 64) and (139, 154), and the
first four `expect` statements hold the bits of these numbers. With
`accumulate` the statement adds the product to the old cells of the output.
The output must then be a `read_write` loan. After the second `gemm` the
cells hold the rows (116, 128) and (278, 308). The function ends with the
releases of its loans and the drops of its three owners.

A `gemm` statement can also scale the product and the old output with
coefficients, as
[Matrix products](../linalg/maps-and-gemm.md#matrix-products) describes.

The module `complex` of the package does the same with `ComplexSmooth` and
cells of `Complex<F64>`. It multiplies the matrix with the rows (1, i, 2) and
(0, 1, −i) by the matrix with the rows (1, 0), (2, 1) and (0, i). The
product has the rows (1 + 2i, 3i) and (2, 2).

## Equal dimensions are not enough

Spaces and bases have
[nominal identity](../appendix/glossary.md#nominal-identity): a space is the
statement that declares it. In this program `other` has the implementation
and the dimension of `v`, but it is another space:

```vast
{{#include ../../examples/reject/packages/other-space/main.vast}}
```

```text
{{#include ../../examples/reject/packages/other-space.stderr}}
```

The notes name the bases, the spaces and the maps of the statement, and the
place where the program introduced each of them.

## Building a numerical program

Check the example from the repository root:

```sh
target/debug/vastitas check --manifest-path examples/packages/numerical/Vastitas.toml
```

A build needs more. A
[*product statement*](../appendix/glossary.md#product-statement) is a
statement whose execution calls the numerical library: `gemm`, its
counterpart `runtime_gemm` for sizes that the program computes, and the
pairings and contractions of the later sections. `vastitas build` links a numerical
runtime and the OpenBLAS library for a program whose entry point reaches a
product statement, and the command must say where the library is:

```sh
target/debug/vastitas build --manifest-path examples/packages/numerical/Vastitas.toml \
  --openblas-prefix "$PWD/target/openblas-0.3.34" -o target/numerical-example
./target/numerical-example
```

The program prints `42`. [Numerical builds](cli.md#numerical-builds) in
Appendix A gives the version of OpenBLAS that the compiler accepts and the
command that builds it into the prefix. On Linux the build command also
takes `--native-cc cc`.

Without `--openblas-prefix` the build of such a program is an error. A
program whose entry point reaches no product statement builds without the
library, and its build rejects the option. The examples of the later
sections that reach a product statement build in the same way, each with its
own manifest.

## Maps as parameters

A resource function receives spaces, bases and maps through parameters. The
types of these parameters name earlier parameters. `Space<L, n>` is the type
of a space of dimension `n` of the linear implementation `L`. `Basis<u>` is
the type of a basis of the space that the parameter `u` receives.
`ReadMap<bs, bt>` is the type of a map from the space of `bs` to the space of
`bt` whose loan permits reading. `WriteMap` and `ReadWriteMap` are the types
for the two other kinds of loans.

A call must pass a basis of the space that it passes, and a map between the
bases that it passes. Another basis of the same space does not fit:

```vast
{{#include ../../examples/reject/packages/other-basis/main.vast}}
```

```text
{{#include ../../examples/reject/packages/other-basis.stderr}}
```

The diagnostic names the argument, the parameter, the basis of the map and
the basis that the parameter requires. Its notes point to the declarations
of both bases and of the parameter.

## Duals, conjugates and adjoints

<a id="duals-conjugates-adjoints-and-metrics"></a>A product never transposes or conjugates a matrix. A program that needs the
transpose or the conjugate transpose declares the map that has this matrix.
Such a map lies between other spaces, and the program declares them too.
[`examples/packages/linear-transforms`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/linear-transforms)
begins with these declarations:

```vast
{{#include ../../examples/packages/linear-transforms/src/main.vast:declarations}}
```

- `involution sigma = canonical(v);` declares the
  [*involution*](../appendix/glossary.md#involution) of the coefficients:
  complex conjugation for a complex linear implementation, and the identity
  for a real one.
- `space vd = dual(v);` declares the dual space of `v`, and
  `space vc = conjugate(v, sigma);` its conjugate space. Each is a different
  space from `v`.
- `basis bvd = derived(bv, vd);` declares the dual basis of `bv`. In a
  conjugate space, `derived` declares the conjugate basis.
- `metric hv = orthonormal(bv, sigma);` declares a
  [*metric*](../appendix/glossary.md#metric): a Hermitian form on `v` whose
  Gram matrix in the basis `bv` is the identity. The Gram matrix of a form
  holds its values on the pairs of basis vectors. `diagonal(bw, sigma, [1])`
  lists the diagonal entries of a Gram matrix. A metric is data that the
  program declares. The compiler never reads one from the cells of a buffer.

For a map `a` from `v` to `w` with the matrix `A`, a program can declare
three [*transformed maps*](../appendix/glossary.md#transformed-map):

| Statement | Map | Matrix |
| --- | --- | --- |
| `map d = dual(a, bwd, bvd);` | From the dual of `w` to the dual of `v` | The transpose of `A` |
| `map c = conjugate(a, bvc, bwc, sigma);` | From the conjugate of `v` to the conjugate of `w` | The conjugate of every entry of `A` |
| `map h = adjoint(a, hv, hw);` | From `w` to `v` | The conjugate transpose of `A` |

No statement of the table copies a cell. A transformed map reads the cells
of `a`, and a product reads them transposed or conjugated. `adjoint` needs
two metrics whose Gram matrices are the identity.

Two functions of the example multiply with the adjoint of a map:

```vast
{{#include ../../examples/packages/linear-transforms/src/main.vast:adjoint-into}}
```

```vast
{{#include ../../examples/packages/linear-transforms/src/main.vast:multiply}}
```

The parameter types state what the first function needs.
`OrthonormalMetric<bv, sigma>` is the type of a metric on `bv` whose Gram
matrix is the identity. `map transformed = adjoint(input, hv, hw);` declares
the adjoint. While `transformed` is live, `input` gives no access, and
`release(transformed);` ends it.

`main` of the example applies the three transforms to the matrix with the one
entry i. The dual has the entry i, and the conjugate and the adjoint have the
entry −i. The program prints `42`.

For other metrics the entries of the adjoint also depend on the two Gram
matrices, so the adjoint is not a view of the cells of `a`. The statement
`adjoint_into(a, out, hv, hw, NativeFast);` writes the matrix of the adjoint
to the map `out` of the caller. The function `adjoint_into` above is a
function of the example, not this statement.
[Adjoints for diagonal metrics](../linalg/transforms-and-metrics.md#adjoints-for-diagonal-metrics)
gives the entries.

## Vectors and pairings

A [*vector*](../appendix/glossary.md#vector) presents a loan as the column of
coordinates of a vector in a basis. `fill`, `store`, `expect` and `copy` may
name a vector in place of its loan. These functions of
[`examples/packages/vector-cells`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/vector-cells)
write the cells of a vector and copy them to another vector:

```vast
{{#include ../../examples/packages/vector-cells/src/main.vast:cells}}
```

`WriteVector<bv> initializes` promises that the function writes every cell
of the vector. `main` of the example declares the vectors with
`vector e = view(cells, bv);`, calls the two functions and reads the cells
back. The program has no product statement, so it builds without the
library, and it prints `42`.

A pairing computes one number from two vectors and writes it to a view with
one cell:

- `evaluate(phi, x, out, overwrite, NativeFast);` applies a covector, a
  vector of the dual space, to a vector. `phi` must be a vector in the dual basis that the program derived
  from the basis of `x`.
- `hermitian(xc, y, out, h, overwrite, NativeFast);` computes the Hermitian
  form of a metric `h` whose Gram matrix is the identity. `xc` is a vector
  in the conjugate basis, such as the conjugate vector that
  `vector xc = conjugate(x, bvc, sigma);` declares.

[Pairings](../linalg/transforms-and-metrics.md#pairings) shows both in a
program and gives the pairing for a diagonal metric.

## Tensor networks

A `contract` block writes the composite of two maps as a
[*network*](../appendix/glossary.md#network): a graph whose nodes are the
maps and whose edge is the contraction.
[`examples/packages/finite_network`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/finite_network)
computes the product of this chapter in that form:

```vast
{{#include ../../examples/packages/finite_network/src/real/mod.vast:network}}
```

- Each `occurrence` is a node that stands for one use of a map. It has two
  [*ports*](../appendix/glossary.md#port): `.input` stands for the dual of
  the source space of the map, and `.output` for its target space.
- `edge(a.input, b.output);` contracts the input of `a` with the output of
  `b`. The source basis of `left` must be the target basis of `right`.
- `input` and `output` name the two ports that stay free. They are the source
  and the target of the result, and `destination` must be a map between
  their bases.

The block computes `left` after `right`, the product of the `gemm` statement
above. It inserts no conjugation, no metric and no change of basis. The
program prints `42`.

Larger networks contract
[*tensors*](../appendix/glossary.md#tensor). A tensor presents a loan as an
array with two or three axes, each indexed by a basis. The program writes
every step itself:

- `pack3` copies a tensor to another arrangement of its axes, and
  `contract3` contracts a tensor of three axes with one of two.
  [Packing and contraction](../linalg/networks-and-packing.md#packing-and-contraction)
  describes both.
- `contract_tree` contracts several tensors along the edges of a tree. Its
  `plan` gives the order of the contractions, every copy and every buffer.
  The compiler searches for no order and inserts no copy.
  [Contraction trees](../linalg/networks-and-packing.md#contraction-trees)
  describes the plan.
- A `cache` records that one tensor holds the packing of another, so that a
  later contraction can use the packing again while the record is valid.
  [Caches](../linalg/networks-and-packing.md#caches) says when it is.

## Products at sizes that the program computes

The `runtime_` statements of
[the storage chapter](storage.md#sizes-that-the-program-computes) have
counterparts for maps.
[`examples/packages/runtime-shapes`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/runtime-shapes)
multiplies two maps whose dimensions are parameters:

```vast
{{#include ../../examples/packages/runtime-shapes/src/main.vast:multiply}}
```

`RuntimeSpace<L, m>` is the type of a space whose dimension is the extent
`m`. `RuntimeBasis<u>` and `RuntimeMap<bs, bt, read>` are the types of a
basis and of a map. The caller declares the spaces and bases from its
extents:

```vast
{{#include ../../examples/packages/runtime-shapes/src/main.vast:spaces}}
```

`main` runs the product at two sizes in one executable:

```vast
{{#include ../../examples/packages/runtime-shapes/src/main.vast:main}}
```

The compiler checks the bases of `runtime_gemm` as it checks the bases of
`gemm`. An extent never shows that two spaces or two bases are the same. The
executable checks the sizes when the program runs. `runtime_gemm` is a
product statement, so the build of this example takes `--openblas-prefix`.
The program checks its own results and prints `0`.
[Runtime maps](../storage/resource-programs.md#runtime-maps) gives the
statements and their rules.

> **What is checked.** The compiler resolves every space, basis and metric
> of a statement itself, and it accepts a product only when the bases of its
> maps fit. Equal dimensions never suffice. An executable
> checks the views and the sizes of an operation before its first write and
> then calls the native routine. The
> [proofs](../language/guarantees.md#nominal-identity) are about the checked
> program. Its numerical operations keep the spaces and the bases of their
> maps. The operation that the checker schedules for a network or a pairing
> conjugates what its operands state and nothing else. No check and
> no theorem covers what the native library computes. A computed cell is a
> binary64 result of that library. It is not a product of real numbers, and
> nothing promises the same bits on two platforms, as
> [Floating-point values](../language/guarantees.md#floating-point-values)
> says.

## See also

- [Numerical maps](../linalg/maps-and-gemm.md): the rules of this chapter.
  [Linear implementations](../linalg/maps-and-gemm.md#linear-implementations),
  [Spaces and bases](../linalg/maps-and-gemm.md#spaces-and-bases),
  [Maps](../linalg/maps-and-gemm.md#maps) and
  [Matrix products](../linalg/maps-and-gemm.md#matrix-products) cover the
  first sections.
- [Map parameters](../linalg/maps-and-gemm.md#map-parameters): the parameter
  types of spaces, bases and maps.
- [Owned maps](../linalg/maps-and-gemm.md#owned-maps) and
  [Owned-map packages](../linalg/maps-and-gemm.md#owned-map-packages): maps
  that own their buffers, which a function can return.
- [Building a numerical program](../linalg/maps-and-gemm.md#building-a-numerical-program):
  the product statements and the rules of the build options.
- [Transforms, evaluation and metrics](../linalg/transforms-and-metrics.md):
  dual and conjugate spaces, metrics, transformed maps, vectors, pairings
  and their parameter types.
- [Networks, packing and contraction trees](../linalg/networks-and-packing.md):
  two-map networks, tensors, packing, contraction trees and caches.
- [Runtime maps](../storage/resource-programs.md#runtime-maps): spaces, maps
  and products with runtime extents.
- [The GEMM contract](../storage-ownership.md#the-gemm-contract): what a
  product reads and writes, and its cost.
- [Nothing implicit](../language/guarantees.md#nothing-implicit),
  [Nominal identity](../language/guarantees.md#nominal-identity) and
  [Floating-point values](../language/guarantees.md#floating-point-values)
  in Guarantees.
- [Numerical backend](../internals/numerical-backend.md): how the compiler
  checks and runs these statements.
