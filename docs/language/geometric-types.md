# Geometric types

The core language has a finite fragment of affine geometry. It has affine
objects over a coefficient marker, the points of an object and the morphisms
between objects. An existential package hides an object together with a point
on it. The checker tracks the **identity** of every object, so that a point of
one object is never used as a point of another.

> **Syntax**
>
> ```text
> GeometricType -> SettingType | PointType | MorphismType | PointedType
> SettingType -> `Scheme` | `CInfScheme`
> PointType -> `Point` `<` Endpoint `,` Endpoint `>`
> MorphismType -> `Morphism` `<` Endpoint `,` Endpoint `>`
> PointedType -> `Pointed` `<` SettingType `,` Marker `>`
> Endpoint -> IDENTIFIER | `Base` `(` Marker `)`
> Marker -> `QQ` | `CInfReal`
> ```

| Type | Values |
| --- | --- |
| `Scheme` | An affine descriptor object of the ordinary setting |
| `CInfScheme` | An affine descriptor object of the smooth setting |
| `Point<X, S>` | A point of `X` with values in `S`: `X` is its **target** and `S` its **test object** |
| `Morphism<X, Y>` | A morphism with **source** `X` and **target** `Y` |
| `Pointed<Scheme, QQ>`, `Pointed<CInfScheme, CInfReal>` | An [existential package](#existential-packages) of an object and a point on it |

A **descriptor object** records only its dimension. The endpoints of point and
morphism types are objects: an object parameter or binding, named by its
identifier, or a base object `Base(K)`.

Rules:

- An endpoint identifier must name an object parameter or binding in scope. A
  name that is not in scope is an error (`E_NAME` in flat mode, `E_TYPE` in
  manifest mode). A binding that is not an object, and a reserved name, are
  errors (`E_TYPE`).
- The argument of `Base` in a type must be `QQ` or `CInfReal`, and the
  arguments of `Pointed` must be a setting and then a marker. Another name
  there is an error (`E_TYPE`).

In manifest mode, [Geometry compatibility exports](../packages.md#geometry-compatibility-exports)
says which programs use the types and operations of this chapter.

## Settings and markers

The ordinary **setting** is `Scheme`, and the smooth setting is `CInfScheme`.
Each setting has one **coefficient marker**: `QQ` for `Scheme` and `CInfReal`
for `CInfScheme`. `Base(K)` is the **base object** over the marker `K`, the
object of dimension zero that is the test object of the points of `origin`. A
marker is a static name, and the base object is distinct from it.

Rules:

- The first argument of `Affine` and of `Base` must be the name `QQ` or
  `CInfReal`. A call without arguments, or another expression there, is an
  error (`E_RING`).
- A marker is not a value. A marker in any other place is an error (`E_RING`
  in flat mode, `E_NAME` in manifest mode), and a call of a marker is an error
  (`E_NAME`).
- The two endpoints of a point type or of a morphism type must be objects over
  the same marker. Other endpoints are an error (`E_BASE`).
- No conversion exists between the two settings. An object of one setting
  where an annotation or a parameter requires the other is an error
  (`E_TYPE`). Arguments of `compose` or `apply` over different markers are an
  error (`E_ENDPOINT`).
- The setting and the marker of a `Pointed` type must belong together.
  `Pointed<Scheme, CInfReal>` is an error (`E_BASE`).

## Operations

These built-in functions construct and use geometric values. Their names are
[reserved](lexical-structure.md#reserved-names).
`Affine(CInfReal, n)` builds a descriptor object. It is not a smooth affine
object with coordinates, smooth maps and covectors. Those are declared with
`indexed affine`, as [Smooth affine objects](smooth-declarations.md#smooth-affine-objects)
describes.

| Call | Arguments | Result |
| --- | --- | --- |
| `Affine(QQ, n)` | `n: Nat` | A fresh object of dimension `n`, of type `Scheme` |
| `Affine(CInfReal, n)` | `n: Nat` | A fresh object of dimension `n`, of type `CInfScheme` |
| `Base(K)` | A marker `K` | The base object over `K` |
| `origin(X)` | An object `X` over `K` | The zero point of `X`, of type `Point<X, Base(K)>` |
| `id(X)` | An object `X` | The identity morphism, of type `Morphism<X, X>` |
| `compose(g, f)` | `f: Morphism<X, Y>`, `g: Morphism<Y, Z>` | `g` after `f`, of type `Morphism<X, Z>` |
| `apply(f, p)` | `f: Morphism<X, Y>`, `p: Point<X, S>` | The image of `p`, of type `Point<Y, S>` |
| `dimension(X)` | An object `X` | The dimension of `X`, of type `Nat` |

Rules:

- A call must have the number of arguments that the table gives. Another
  number is an error (`E_ARITY`), except for `Affine()` and `Base()`, which
  the rule on markers rejects.
- The dimension argument of `Affine` must have type `Nat` (`E_TYPE`). It is
  the expected type of a literal there.
- The source of `g` must be the target of `f` in `compose(g, f)`, and the
  source of `f` must be the target of `p` in `apply(f, p)`. Another object is
  an error (`E_ENDPOINT`).
- An argument of `origin`, `id` or `dimension` that is not an object is an
  error (`E_TYPE`). So is an argument of `compose` or `apply` that is neither a
  point nor a morphism.
- A point where `compose` or `apply` requires a morphism, and a morphism where
  `apply` requires a point, are errors (`E_ENDPOINT`).
- An `E_ENDPOINT` diagnostic names the first requirement that fails: the
  family of an argument, `Point` or `Morphism`, then an endpoint, a marker or
  a classification. It gives the required and the supplied value.

## Object identity

Every object has a [nominal identity](../appendix/glossary.md#nominal-identity):
its identity comes from the construction that created it, never from its
structure. Two objects are the same object only when their identities are the
same. Where a parameter type names an earlier parameter, a call substitutes the
object of the argument, as [Calls](functions.md#calls) says.

A diagnostic about identities names the objects by their bindings. It adds a
note for the place that introduced each identity, which is an `Affine`
construction, a parameter, a call, an `unpack` or an `if`. Two bindings of one
object, such as an alias, share that note. Names only help the reader: two
objects with the same name in different places are different objects.

Rules:

- Each call of `Affine` creates an object with a fresh identity.
- A binding to an object, such as `let Y = X;`, denotes the same object as
  `X`.
- Equal settings, markers, dimensions or run-time descriptors never make two
  objects the same. Objects have no equality operation (`E_OPERATOR`).
- A call of a function that returns an object gives an object with a fresh
  identity, even when the function returns its argument. The checker infers no
  identities across functions.
- An `if` expression whose branches are different objects gives an object with
  a fresh identity. An `if` expression whose branches are the same object gives
  that object.

In this program `X` and `Y` have the same dimension, but `p` is a point of `X`:

```vast
{{#include ../../examples/reject/geometric-types/wrong-endpoint.vast}}
```

```text
{{#include ../../examples/reject/geometric-types/wrong-endpoint.stderr}}
```

> **Implementation note.** An object is stored at run time as a descriptor of
> its dimension, and `origin` allocates no array of coordinates. The checker
> erases identities only after it has checked the program.

## Existential packages

An **existential package** of type `Pointed<Scheme, QQ>` or
`Pointed<CInfScheme, CInfReal>` hides an object together with a point of it
whose test object is the base object. [`pack`](expressions.md#pack-expressions)
builds an existential package, and [`unpack`](statements.md#unpack-statements)
opens one. A result type names only the parameters of its function, as
[Functions](functions.md) says, so a function returns a point of an object of
its body only inside an existential package.

Rules:

- In `pack { scheme: X, point: p }`, `X` must be an object (`E_TYPE`).
- The point `p` must have the target `X` and the test object `Base(K)`, where
  `K` is the marker of `X`. Another point, and a value that is not a point,
  are errors (`E_ENDPOINT`). A function value there is an error (`E_TYPE`).
- Each `unpack` gives the object a fresh identity, even when it opens the same
  existential package twice.
- A value whose type names an object that a block introduced must not leave
  that block. A block introduces an object with a call of `Affine`, an
  `unpack`, a call of a function that returns an object, or an `if` over
  different objects. A point or morphism that leaves without its object is an
  error (`E_ESCAPE`), as in `{ origin(Affine(QQ, 2)) }`. Packing the object
  with its point is valid.
- An object itself is an immutable value, and it may leave its block.

This program builds an existential package, opens it and keeps the point on
its object:

```vast
{{#include ../../examples/book/geometric-types/pointed-origin.vast}}
```

The executable prints `42`. Without its object the point cannot leave the
block that opened the existential package:

```vast
{{#include ../../examples/reject/geometric-types/escaping-point.vast}}
```

```text
{{#include ../../examples/reject/geometric-types/escaping-point.stderr}}
```

## Scope of the geometric core

The geometric core covers the objects, operations and existential packages of
this chapter.
It does not implement coordinate rings, generalized points other than the
points above, arbitrary algebraic or smooth maps, or a decision procedure for
isomorphisms of schemes. Smooth affine geometry with coordinates, maps and
covectors is in [Smooth affine declarations](smooth-declarations.md), and
presented affine geometry in [Presented affine geometry](../affine-geometry.md).
