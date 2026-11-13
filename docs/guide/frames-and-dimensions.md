# Frames and physical dimensions

This chapter builds one program step by step. It describes vectors on the
plane by their components in bases other than the coordinate basis, changes
from one basis to another, and writes the derivative of a map as a matrix in
two pairs of bases. It then gives the coordinates of a chart physical
meanings, a length and a time, and lets the compiler check that a metric on
the chart adds quantities of one dimension. Every number in the program is a
rational number, and the program prints `42` only when every observation
holds.

The program is
[`examples/packages/stdlib-frames/main.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/packages/stdlib-frames/main.vast).
Run it from the repository root:

```sh
python3 scripts/build_stdlib_package.py
target/debug/vastitas build --manifest-path examples/packages/stdlib-frames/Vastitas.toml -o target/stdlib-frames
./target/stdlib-frames
```

## Two libraries

The program uses the standard library and the package `nature`, which gives
physical meanings to the objects of the standard library. Its manifest
depends on both by path:

```toml
{{#include ../../examples/packages/stdlib-frames/Vastitas.toml}}
```

The program imports the smooth profile of the
[previous chapter](smooth-geometry.md), the frame families of the standard
library, and two families and two quantity kinds of `nature::dimension`:

```vast
{{#include ../../examples/packages/stdlib-frames/main.vast:imports}}
```

| Name | Meaning |
| --- | --- |
| `Frame<X>` | The type that the declaration of a frame of `X` names |
| `Coords<b>` | The type of the arrays of vectors in the frame `b` |
| `FrameMap<b, c>` | The type of the arrays of linear maps from the frame `b` to the frame `c` |
| `Reading<X>` | The type that a reading of the coordinates of `X` names |
| `PhysicalMetric<X>` | The type that a physical interpretation of a metric on `X` names |
| `Length`, `Time` | Two quantity kinds: what a coordinate measures |

The sections below introduce each of them where the program uses it.

## Frames of the plane

A vector at a point of the plane has two components, one for each
coordinate. They are its components in the coordinate basis: (3, 2) is three
times the unit vector of `x` plus twice the unit vector of `y`. Any two
vectors that are not parallel form a basis as well. A
[*frame*](../appendix/glossary.md#frame) chooses such a basis at every point
of an object. The program declares four frames:

```vast
{{#include ../../examples/packages/stdlib-frames/main.vast:frames}}
```

`columns(…)` lists the frame vectors, each in the coordinates of the object.
The frame `b` has the frame vectors (1, 0) and (1, 2) at every point. The
[*coordinate frame*](../appendix/glossary.md#coordinate-frame) `e` has the
unit vectors of the coordinates. The frame `l` of the line has the frame
vector 2, twice the unit vector of `t`. The frame vectors of `r` depend on
the point: at (x, y) they are (1, 0) and (x, 1).

The frame vectors must form a basis at every point. For a frame whose
columns are constants, such as `b`, the compiler computes the inverse of the
matrix of the columns and checks it. A frame whose columns depend on the
point declares its inverse after `inverse =`, and the compiler checks that
the two matrices are inverse at every point. The frame `r` needs it:

```vast
{{#include ../../examples/reject/packages/frame-missing-inverse/main.vast:declaration}}
```

```text
{{#include ../../examples/reject/packages/frame-missing-inverse.stderr}}
```

## Arrays in a frame

The program builds the vector v = (3, 2) at the point p = (1, 2), and its
components in the frame `b`:

```vast
{{#include ../../examples/packages/stdlib-frames/main.vast:arrays}}
```

```vast
{{#include ../../examples/packages/stdlib-frames/main.vast:encode}}
```

The vector v is 2 · (1, 0) + 1 · (1, 2), so its components in `b` are 2
and 1. The binding `frame_encode(Tangent, Coords, frame = b)` computes them:
`to_b(v)` is the [*frame array*](../appendix/glossary.md#frame-array) (2, 1)
at p, of type `Coords<b>`. Codes 1 and 2 of [`main`](#the-observations) read
its components and check that `from_b`, the binding `frame_decode`, turns it
back into v.

The frame of an array is part of its type: `Coords<b>` and `Coords<r>` are
two types. The point of an array is a value, as the point of a vector is.
`frame_vector(Coords, Smooth, frame = r)` builds an array in `r` from a point
and one integer for each frame vector, as `vplane` builds a vector.

## Changing frames

The same vector has an array in each frame. A
[*transition*](../appendix/glossary.md#transition) turns the array of a
vector in one frame into its array in another frame:

```vast
{{#include ../../examples/packages/stdlib-frames/main.vast:changes}}
```

`b_to_e(p)` is the transition from `b` to the coordinate frame at p, and
`apply_map` applies it to an array. Applied to `w`, it gives (3, 2), the
components of v (code 3). At p the frame vectors of `r` are (1, 0) and
(1, 1), so the array (1, 2) in `r` is 1 · (1, 0) + 2 · (1, 1), the vector v
again. The transition from `r` to `b` turns it into `w` (code 4).

A transition takes arrays in its source frame only. The checker compares the
frames of the operands before the compiler generates code. In a program with
the declarations of this chapter, the following function applies the
transition from `b` to an array in `r`:

```vast
{{#include ../../examples/reject/packages/frame-apply-frame/main.vast:program}}
```

```text
{{#include ../../examples/reject/packages/frame-apply-frame.stderr}}
```

The checker cannot compare points, which are run-time values. A transition
at p applied to an array at another point gives the
[*failure value*](../appendix/glossary.md#failure-value), as a pullback of a
seed over the wrong point does.

## The matrix of a map

The derivative of a map at a point is a linear map between the tangent
fibers, and a pair of frames writes it as a matrix, a
[*map array*](../appendix/glossary.md#map-array):

```vast
{{#include ../../examples/packages/stdlib-frames/main.vast:matrices}}
```

`g` sends (x, y) to x² + y, so its derivative at p = (1, 2) sends a vector
(a, b) to 2a + b. In the coordinate frame `e` of the plane and the frame `l`
of the line, whose frame vector is 2, the matrix of the derivative is
(1, 1/2) (code 5). In the frames `b` and `l` it is (1, 2) (code 6): the
derivative sends the frame vector (1, 0) to 2, which is 1 · 2, and (1, 2) to
4, which is 2 · 2.

The two matrices differ, and they describe one linear map. `then` composes
map arrays, and `then(matrix_el(g(), p), b_to_e(p))` first changes from `b`
to `e` and then applies the matrix in `e` and `l`. It equals the matrix in
`b` and `l` (code 7). `frame_matrix` computes the matrix with the reverse
pass of the [previous chapter](smooth-geometry.md#the-forward-pass-and-the-reverse-pass),
on the map as the program writes it.

## A chart with a length and a time

The second object of the program is a chart, whose coordinate `x` measures a
length and whose coordinate `t` measures a time. A
[*reading*](../appendix/glossary.md#reading) says so:

```vast
{{#include ../../examples/packages/stdlib-frames/main.vast:chart}}
```

`Length` and `Time` are [*quantity kinds*](../appendix/glossary.md#quantity-kind)
of `nature::dimension`. `Length` has the
[*physical dimension*](../appendix/glossary.md#physical-dimension) L and
`Time` the physical dimension T, two
[*base dimensions*](../appendix/glossary.md#base-dimension) of the library.

The reading changes nothing about the chart. Its use is a
[*physical interpretation*](../appendix/glossary.md#physical-interpretation)
of a metric on the chart, which the compiler checks against the reading. The
Euclidean metric dx² + dt² adds a squared length to a squared time. In the
following program, with the chart and the reading of this chapter, the
compiler rejects its interpretation:

```vast
{{#include ../../examples/reject/packages/dimension-dx2-dt2/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/dimension-dx2-dt2.stderr}}
```

The metric `E` itself stays valid. Only its interpretation is an error.

## Scales and a scaled metric

To add a length and a time, a metric divides each by a reference quantity of
its own kind, a [*scale*](../appendix/glossary.md#scale):

```vast
{{#include ../../examples/packages/stdlib-frames/main.vast:scaled}}
```

`l0` is a length of magnitude 3 and `t0` a time of magnitude 2. The metric
`G` has the Gram matrix diag(1/9, 1/4), which is dx²/l0² + dt²/t0². The
interpretation `PG` writes the entries of `G` with the scales:
`l0^-2` is 1/3² = 1/9 and `t0^-2` is 1/2² = 1/4. The compiler evaluates the
entries and compares them with the Gram matrix of `G`. It then checks that
each term has one physical dimension: dx²/l0² is L² · L⁻², which is
dimensionless, and so is dt²/t0².

## The gradient

The interpretation is a checked statement about `G`, and it changes no
value. The program computes a gradient under `G` as the
[previous chapter](smooth-geometry.md#metrics-and-gradients) does:

```vast
{{#include ../../examples/packages/stdlib-frames/main.vast:gradient}}
```

`h` sends (x, t) to x + t, so its differential is (1, 1) at every point. The
inverse of the Gram matrix of `G` is diag(9, 4), and the gradient is (9, 4)
(code 8). With other scales, `G` and the gradient would differ: the scales
fix the metric, and the metric fixes the gradient.

## The observations

Two helper functions keep `main` short, as in the previous chapter:

```vast
{{#include ../../examples/packages/stdlib-frames/main.vast:helpers}}
```

Each observation adds its code to 42 when it fails:

```vast
{{#include ../../examples/packages/stdlib-frames/main.vast:main}}
```

> **What is checked.** The checker rejects an array, a map array or a vector
> in the wrong frame or over the wrong object before the compiler generates
> code. It checks that the frame vectors of every frame form a basis at every
> point, and it checks every physical interpretation against its metric and
> its reading. The [proofs](../verification.md#frames-and-physical-dimensions) cover the frames, encoding
> and decoding, transitions, the matrices of maps and their composites, the
> pairing in frames, Gram matrices in frames, and the meaning of a physical
> interpretation. They also cover the comparison of frames and matrices with
> bases and derivatives of real analysis, and the fact that the declarations
> of `nature` change no other declaration and no value. Tests cover native
> execution, the diagnostics and agreement with an independent reference
> program. An array over the wrong point of the right object gives the
> failure value at run time, not an error of the compiler.

## See also

- [Frames](../language/frames.md): the frame families, frame declarations,
  the frame primitives and their rules.
  [Frame declarations](../language/frames.md#frame-declarations) gives
  `columns(…)`, `coordinates` and `inverse = …`.
- [Encoding and decoding](../language/frames.md#encoding-and-decoding),
  [Map arrays and transitions](../language/frames.md#map-arrays-and-transitions)
  and [Contraction in frames](../language/frames.md#contraction-in-frames):
  the values of the frame primitives.
- [Operand checks](../language/frames.md#operand-checks): the errors of a
  call, and [The Gram matrix in a frame](../language/frames.md#the-gram-matrix-in-a-frame).
- [Physical dimensions](../language/physical-dimensions.md): base
  dimensions, quantity kinds, readings, scales and physical interpretations.
  [Physical interpretations](../language/physical-dimensions.md#physical-interpretations)
  gives `euclidean`, `gram(…)`, `normalized(…)` and `value =`.
- [The library nature::dimension](../language/physical-dimensions.md#the-library-naturedimension):
  its declarations and how to import them.
- [Smooth affine declarations](../language/smooth-declarations.md): objects,
  maps, fibers, metrics and `sharp`.
