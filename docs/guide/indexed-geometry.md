# Indexed declarations and the geometry library

Vastitas types can mention geometric objects. A point's type names the object
it lies on, and a morphism's type names its source and target. This chapter
starts with the built-in geometric core, moves to the standard geometry library
and ends with declaring an indexed profile of your own.

## Objects, points and morphisms

The core has a deliberately small set of forms:

| Form | Meaning |
| --- | --- |
| `Affine(QQ, n)` | An ordinary affine object of dimension `n` over the rationals |
| `Affine(CInfReal, n)` | A smooth affine object over the smooth reals |
| `Base(K)` | The base object, distinct from the coefficient marker `K` |
| `origin(X)` | The zero point of `X`, with test object `Base(K)` |
| `id(X)` | The identity morphism on `X` |
| `compose(g, f)` | `g` after `f`; the middle endpoint must agree |
| `apply(f, p)` | Apply a morphism to a point on its source |
| `dimension(X)` | The dimension of `X`, a `Nat` |

`Scheme` is the ordinary setting and `CInfScheme` the smooth one. There is no
implicit bridge between them.
[`examples/smooth.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/smooth.vast)
works in the smooth setting:

```vast
{{#include ../../examples/smooth.vast}}
```

```sh
target/debug/vastitas build examples/smooth.vast -o target/smooth
./target/smooth
```

The program prints `2`.

`Affine(CInfReal, n)` builds a descriptor object that records only its
dimension. Smooth real affine space with named coordinates, smooth maps and
covectors is a separate declaration, `Affine(n)[c₁, …, cₙ]`; see
[smooth affine declarations](../language/smooth-declarations.md).

## Identity is nominal

`Point<X, S>` is an `S`-valued point of `X`, and `Morphism<X, Y>` carries both
endpoints. The checker compares **object identities**, never dimensions:

- Every `Affine(...)` construction has a fresh identity. An alias keeps it.
- A function that returns an object gives each call a fresh identity.
- Equal settings, bases, dimensions or descriptors never identify two objects.

To return a point together with its object, pack them. `Pointed<Scheme, QQ>`
hides an object with a point on it. Each `unpack` opens the package with a fresh
scoped identity, even when the same package is opened twice. Returning a local
point without its object is rejected; repacking the two together is fine.
[Chapter 1](hello-vastitas.md#a-program-with-geometry) walks through
`examples/pointed.vast`, which does exactly this.

## The standard geometry library

`std::geometry::scheme` and `std::geometry::smooth` declare the same finite
profile as library code, through the indexed declarations shown below. This
demo uses the explicit witness and field syntax of indexed packages.
[`examples/packages/stdlib-geometry/main.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/packages/stdlib-geometry/main.vast):

```vast
{{#include ../../examples/packages/stdlib-geometry/main.vast}}
```

It prints `42`; [Chapter 1](stdlib.md#using-the-standard-library) has the build
commands. The two dimensions add, but nothing lets `p` be used in `Y`.

## Declaring an indexed profile

The library is not privileged. Any package can declare its own markers,
classifications, families, existential packages and primitives with `indexed`
declarations.
[`examples/packages/indexed/geo.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/packages/indexed/geo.vast)
declares a complete ordinary affine profile:

```vast
pub indexed marker QQ;
pub indexed implementation Grid(QQ, affine_descriptor) capabilities(origin, dimension);
pub indexed classification Scheme { parents(); domain(Grid); };
pub indexed global Base(Grid);
pub indexed family Point(object(Scheme), object(Scheme)) = point constraints(same_base(0, 1));
pub indexed family Morphism(object(Scheme), object(Scheme)) = morphism constraints(same_base(0, 1));
pub indexed package Pointed {
    case(Scheme, QQ) { Point(witness, global(Base)); }
};
pub indexed primitive affine = descriptor(Grid);
pub indexed primitive baseObject = global(Base);
pub indexed primitive origin = origin((Scheme, QQ), Point, Base);
pub indexed primitive identity = identity((Scheme, QQ), Morphism);
pub indexed primitive dimension = dimension((Scheme, QQ));
pub indexed primitive compose = compose(Morphism);
pub indexed primitive apply = apply(Morphism, Point);
```

A declaration's identity is its defining package, module and name. Names such as
`Scheme` or `Point` grant nothing by themselves. The checker audits each
primitive against its declared representation, domain, arity and capabilities.

The package root uses the profile through qualified paths:

```vast
{{#include ../../examples/packages/indexed/main.vast}}
```

```sh
cargo run --locked -- check --manifest-path examples/packages/indexed/Vastitas.toml
cargo run --locked -- build --manifest-path examples/packages/indexed/Vastitas.toml -o target/indexed-demo
./target/indexed-demo
# 42
```

A library can also export the legacy spellings (`Scheme`, `Point<X, Base(QQ)>`,
`pack { scheme: ..., point: ... }`) to packages through an explicit, checked
`[geometry_compat]` manifest entry. The standard geometry library's
[manifest](https://github.com/MGYamada/Vastitas/blob/main/stdlib/src/geometry/Vastitas.toml)
does this, so the older syntax keeps working in package mode.

> **What is checked.** Lean composes the declaration audit with the same
> function, dispatch and edit-authority checkers on one input. The exact
> declaration grammar, existential rules and legacy export are in
> [Indexed declarations](../indexed-source.md). Typed total
> evaluation of the returned Core is proved; source operational correspondence
> and native refinement are not. See
> [Acceptance and proof scope](../internals/indexed-checker.md#acceptance-and-proof-scope)
> and the [geometry migration record](../internals/indexed-checker.md#geometry-migration).
