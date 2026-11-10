# Defining an indexed profile

The standard geometry library is a package of indexed declarations, and it
has no special rights. This chapter writes such declarations. An
[*indexed profile*](../appendix/glossary.md#profile) is a set of indexed
declarations that defines one geometric setting: its objects, its types and
its operations.

The profile of this chapter is the module `geo` of
[`examples/packages/indexed`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/indexed).
It declares the ordinary setting of the previous chapter: descriptor objects
over the rational numbers, with their points and morphisms. The sections
follow the file
[`geo.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/packages/indexed/geo.vast)
from its first declaration to its last. Indexed declarations exist only in a
package.

## A marker and an implementation

```vast
{{#include ../../examples/packages/indexed/geo.vast:marker}}
```

An `indexed marker` declaration declares a marker: a name for the
coefficients of objects. A marker is not a value, and it is not an object.

```vast
{{#include ../../examples/packages/indexed/geo.vast:implementation}}
```

An [*implementation*](../appendix/glossary.md#implementation) is one kind
of object. The objects of `Grid` have the marker `QQ`. `affine_descriptor` is
the [*representation*](../appendix/glossary.md#representation) of the
implementation, which says what an object holds: an object of `Grid` is a
descriptor object and records its dimension.

`capabilities(origin, dimension)` lists the
[*capabilities*](../appendix/glossary.md#capability) of the implementation:
the operations that its objects support. This is a second meaning of the
word. It is unrelated to the capabilities `HasEq` and `HasOrder` that a
[method requires](dispatch.md#selectors-and-capabilities).

## A classification

```vast
{{#include ../../examples/packages/indexed/geo.vast:classification}}
```

A [*classification*](../appendix/glossary.md#classification) is a finite
set of implementations under one name. The list after `domain` is the domain
of the classification: `Scheme` holds the one implementation `Grid`. Types
and operations name a classification, and they then hold for the objects of
every implementation in its domain. `parents()` lists the classifications
whose domains contain this one. `Scheme` has none.

## A global object

```vast
{{#include ../../examples/packages/indexed/geo.vast:global}}
```

A [*global object*](../appendix/glossary.md#global-object) is one object
that a declaration names. `Base` is an object of the implementation `Grid`,
with the dimension 0. Every module that sees the declaration names the same
object. The profile uses `Base` as the test object of its points.

## Families of types

```vast
{{#include ../../examples/packages/indexed/geo.vast:families}}
```

A [*family*](../appendix/glossary.md#family) forms types from arguments.
`Point` has two parameters, and `object(Scheme)` says that each takes an
object of the classification `Scheme`. The word after `=` is the
representation of the family, which says what the values of its types are.
With `point`, the type `Point<X, S>` holds the points of `X` with the test
object `S`. With `morphism`, the type `Morphism<X, Y>` holds the morphisms
from `X` to `Y`.

`constraints(same_base(0, 1))` restricts the arguments. The numbers are the
positions of the parameters, counted from 0, and the two objects must have
the same marker.

The name of a declaration chooses nothing. `Point` is a family of points
because its declaration says `point`.

## An existential package type

```vast
{{#include ../../examples/packages/indexed/geo.vast:package}}
```

An `indexed package` declaration declares types of existential packages,
one for each `case`. `Pointed<Scheme, QQ>` is the type of a package that
hides an object of `Scheme` over `QQ`, its
[*witness*](../appendix/glossary.md#witness). The braces list the
[*fields*](../appendix/glossary.md#field): the values that the package
holds beside the witness. Here it holds one value of the family `Point`, a
point of the witness with the test object `Base`.

## Primitives

```vast
{{#include ../../examples/packages/indexed/geo.vast:primitives}}
```

A [*primitive*](../appendix/glossary.md#primitive) is an operation of the
profile. The part after `=` is its
[*primitive binding*](../appendix/glossary.md#primitive-binding), which
fixes the operands and the result:

| Primitive | Operands | Result |
| --- | --- | --- |
| `affine` | A `Nat` | A fresh object of `Grid` with that dimension |
| `baseObject` | None | The global object `Base` |
| `origin` | An object `X` of `Scheme` over `QQ` | The origin of `X`, of type `Point<X, Base>` |
| `identity` | An object `X` of `Scheme` over `QQ` | The identity morphism, of type `Morphism<X, X>` |
| `dimension` | An object `X` of `Scheme` over `QQ` | The dimension of `X`, a `Nat` |
| `compose` | Two morphisms of the family `Morphism` | Their composite |
| `apply` | A morphism and a point | The image of the point |

The bindings form a closed set. A profile chooses among them and names the
declarations that they act on. It defines no operation of its own, and a
binding names no native code.

## Using the profile

The root module of the package declares `mod geo;` and names the
declarations of the profile by paths:

```vast
{{#include ../../examples/packages/indexed/main.vast}}
```

`geo::affine(n)` constructs an object. The `pack` expression states the type
of the package, the witness and the fields. `unpack` binds the witness `Y`
and the point `p`, and `geo::Point<Y, geo::Base>` is the indexed type of a
point of `Y`. A type applies a family of the profile through a path. The
bare names `Point`, `Morphism` and `Pointed` in front of `<` belong to the
core syntax of the previous chapter.

```sh
target/debug/vastitas check --manifest-path examples/packages/indexed/Vastitas.toml
target/debug/vastitas build --manifest-path examples/packages/indexed/Vastitas.toml -o target/indexed-demo
./target/indexed-demo
```

The program prints `42`: `make(41)` hides an object of dimension 41, and
`main` adds 1 to the dimension.

## Capabilities and object types

A profile can have several implementations. The module `shapes` of
[`examples/packages/indexed-objects`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/indexed-objects)
declares two, with different capabilities:

```vast
{{#include ../../examples/packages/indexed-objects/shapes.vast:implementations}}
```

Two classifications group them. `Shape` holds both implementations.
`Measured` holds `Grid` alone and names `Shape` as its parent:

```vast
{{#include ../../examples/packages/indexed-objects/shapes.vast:classifications}}
```

The module has three primitives. `grid` and `plain` construct objects of the
two implementations, and `size` gives the dimension of an object of
`Measured`:

```vast
{{#include ../../examples/packages/indexed-objects/shapes.vast:primitives}}
```

A primitive must be valid for every implementation of the classification
that it names. Every implementation of `Measured` has the capability
`dimension`. `Shape` also holds `Plain`, which lacks it, so the compiler
rejects the same binding over `Shape`, at its declaration:

```vast
{{#include ../../examples/reject/packages/missing-capability/main.vast}}
```

```text
{{#include ../../examples/reject/packages/missing-capability.stderr}}
```

The type of an object is an
[*object type*](../appendix/glossary.md#object-type) `Object<D, K>`, where
`D` names a classification or an implementation and `K` a marker. The root
module of `indexed-objects` uses two object types:

```vast
{{#include ../../examples/packages/indexed-objects/main.vast:object-types}}
```

`shapes::grid(42)` gives an object of type
`Object<shapes::Grid, shapes::QQ>`. `Grid` is in the domains of `Measured`
and of `Shape`, so both `measure` and `hide` accept `X`. The witness `Y` has
the type that the case of `Hidden` declares,
`Object<shapes::Shape, shapes::QQ>`. The program prints `42`.

The object type belongs to a binding, not to the object: two bindings of
one object can have different object types. An annotation with a wider
object type hides the implementation, and `size` no longer accepts the
binding:

```vast
{{#include ../../examples/reject/packages/lost-capability/main.vast}}
```

```text
{{#include ../../examples/reject/packages/lost-capability.stderr}}
```

## Each declaration is its own

The identity of an indexed declaration is its owner: its package, its module
and its name. The same text in another module declares another marker,
another implementation and other primitives:

```vast
{{#include ../../examples/reject/packages/copied-profile/main.vast}}
```

```text
{{#include ../../examples/reject/packages/copied-profile.stderr}}
```

The diagnostic names the two markers by their owners. A program that wants
one profile in two modules declares it once and imports it. The standard
library does this: `std::geometry::scheme` and `std::geometry::smooth`
reexport one family `Point` from their parent module.

## Beyond this profile

The geometry package of the standard library is a profile like `geo`, with
one implementation, one classification and one base object for each setting.
Its
[manifest](https://github.com/MGYamada/Vastitas/blob/main/stdlib/src/geometry/Vastitas.toml)
also holds the export that gives the core syntax its meaning in a package.
[Core geometry syntax](../indexed-source.md#core-geometry-syntax) lists the
entries of an export.

The declarations of this chapter give descriptor objects. Their points are
origins and images of origins, and their morphisms are identities and
composites of identities. An object has no coordinates, and a morphism has
no formula. Other kinds of indexed declarations declare richer objects. The
next chapter, [Presented affine geometry](affine-geometry.md), declares
objects by coordinates and polynomial equations.

> **What is checked.** The compiler checks every indexed declaration, even
> one that no function uses. Each path must name a declaration of the kind
> that its place requires. Each primitive must fit the capabilities and the
> families that it names, and each field of a package the family that it
> applies. The checker resolves the paths and makes these checks itself, and
> it trusts no claim about a declaration from the part of the compiler that
> reads the source. [The indexed checker](../internals/indexed-checker.md)
> describes the checks and states what is proved about them. Tests cover the
> diagnostics and native execution.

## See also

- [Indexed declarations](../indexed-source.md): the rules of every kind of
  declaration of this chapter.
- [Markers](../indexed-source.md#markers),
  [Implementations](../indexed-source.md#implementations),
  [Classifications](../indexed-source.md#classifications) and
  [Global objects](../indexed-source.md#global-objects).
- [Object types](../indexed-source.md#object-types): when one object type
  lies within another.
- [Families](../indexed-source.md#families): parameters, constraints and
  representations, including families that take a marker or a number.
- [Existential packages](../indexed-source.md#existential-packages): cases,
  fields, packing and opening.
- [Primitives](../indexed-source.md#primitives): the bindings and the calls
  of primitives.
- [Core geometry syntax](../indexed-source.md#core-geometry-syntax): the
  entries of an export.
- [Appendix D](../appendix/limits.md#other-documented-bounds): the limits on
  indexed declarations.
