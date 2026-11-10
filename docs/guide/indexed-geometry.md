# Indexed declarations and the geometry library

A type can name a geometric object. The type of a point names the object
that the point lies on, and the type of a morphism names its source and its
target. The checker uses these types to keep a point of one object away from
every other object.

This chapter first uses the geometric core that is built into the language.
It then uses the same geometry from the standard library. The library
declares it with
[*indexed declarations*](../appendix/glossary.md#indexed-declaration):
items that begin with `indexed` and give a package objects and types of its
own.

## Objects, points and morphisms

[`examples/book/geometric-types/objects.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/book/geometric-types/objects.vast)
constructs an object, a point and a morphism:

```vast
{{#include ../../examples/book/geometric-types/objects.vast}}
```

`Affine(QQ, 42)` constructs an object: an affine space of dimension 42 over
the rational numbers. `QQ` is a [*marker*](../appendix/glossary.md#marker),
a name for the coefficients, and the type of the object is `Scheme`. The
object is a [*descriptor object*](../appendix/glossary.md#descriptor-object):
it records its dimension and nothing else. It has no coordinates.

`origin(X)` is the zero point of `X`. Its type is `Point<X, Base(QQ)>`. The
first argument is the object that the point lies on. The second is the
[*test object*](../appendix/glossary.md#test-object) of the point, here the
[*base object*](../appendix/glossary.md#base-object) `Base(QQ)`: the object
of dimension zero over `QQ`.

`id(X)` is the identity morphism of `X`, of type `Morphism<X, X>`.
`compose(g, f)` is `g` after `f`, and `apply(f, p)` is the image of the point
`p` under the morphism `f`. `dimension(X)` is the dimension of `X`, a `Nat`.

The second parameter of `carry` has a type that names the first parameter.
`p` is a point of the object that the caller passes as `X`, and the result
is a point of the same object.

```sh
target/debug/vastitas check examples/book/geometric-types/objects.vast
target/debug/vastitas build examples/book/geometric-types/objects.vast -o target/objects
./target/objects
```

The program prints `42`. [Operations](../language/geometric-types.md#operations)
lists the operations with their types.

## Identity is nominal

Every object has a
[*nominal identity*](../appendix/glossary.md#nominal-identity): it is the
object that one construction made. Two objects are the same object only when
they come from the same construction. An equal dimension does not make them
the same:

```vast
{{#include ../../examples/reject/geometric-types/wrong-endpoint.vast}}
```

```text
{{#include ../../examples/reject/geometric-types/wrong-endpoint.stderr}}
```

The notes name the place that introduced each object. Three rules decide
which object a name denotes:

- A binding to an object, such as `let Y = X;`, names the same object as
  `X`.
- Each call of `Affine` constructs an object with a fresh identity.
- A call of a function that returns an object gives an object with a fresh
  identity, even when the function returns its argument.

Objects have no `==`. [Object identity](../language/geometric-types.md#object-identity)
gives the rules.

## Two settings

`Scheme` is the ordinary [*setting*](../appendix/glossary.md#setting), with
the marker `QQ`. The smooth setting is `CInfScheme`, with the marker
`CInfReal`: `Affine(CInfReal, n)` constructs an object of type `CInfScheme`,
and `Base(CInfReal)` is its base object. The operations are the same in both
settings. Nothing converts an object, a point or a morphism of one setting to
the other.

An object of type `CInfScheme` is a descriptor object too. A smooth space
with coordinates, smooth maps and covectors is another kind of object, which
the chapter [Smooth geometry and reverse pullbacks](smooth-geometry.md)
declares.

## Existential packages

The result type of a function can name the parameters of the function and no
object of its body. A function that constructs an object therefore cannot
return a point of it as a `Point`. It returns an
[*existential package*](../appendix/glossary.md#existential-package): a
value that hides an object together with a point of it.
[`examples/smooth.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/smooth.vast)
does this in the smooth setting:

```vast
{{#include ../../examples/smooth.vast}}
```

`Pointed<CInfScheme, CInfReal>` is the type of an existential package of the
smooth setting, and `Pointed<Scheme, QQ>` is the type of the ordinary one.
`pack { scheme: X, point: origin(X) }` builds the package. The `unpack`
statement opens it: it binds `X` to the hidden object and `p` to its point,
of type `Point<X, Base(CInfReal)>`.

```sh
target/debug/vastitas build examples/smooth.vast -o target/smooth
./target/smooth
```

The program prints `2`.

Each `unpack` gives the object a fresh identity, even when a program opens
one package twice. The point is a point of that object, and it cannot leave
the block of its object:

```vast
{{#include ../../examples/reject/geometric-types/escaping-point.vast}}
```

```text
{{#include ../../examples/reject/geometric-types/escaping-point.stderr}}
```

The type of `q` names `X`, and `X` exists only inside the block. A program
that needs the point outside packs it with its object again.
[Existential packages](../language/geometric-types.md#existential-packages)
gives the rules.

## The geometry library

The compiler has the geometric core built in. The standard library declares
the same objects, types and operations as ordinary declarations of a
package, in the modules `std::geometry::scheme` and `std::geometry::smooth`.
[`examples/packages/stdlib-geometry/main.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/packages/stdlib-geometry/main.vast)
uses both modules through paths:

```vast
{{#include ../../examples/packages/stdlib-geometry/main.vast}}
```

The program reads like the programs above, with the names of the library:

- `scheme::pointed(20)` is a function of the library. It packs a fresh object
  of dimension 20 with its origin. `smooth::pointed(22)` does the same in the
  smooth setting.
- `unpack ordinary as { witness: X, fields: [p] };` opens the package.
  `witness` binds the hidden object, and `fields` lists the values that the
  package holds beside it, here one point.
- `scheme::Point<X, scheme::BaseQQ>` is an
  [*indexed type*](../appendix/glossary.md#indexed-type). `Point` is a
  [family](../appendix/glossary.md#family) of types that the library
  declares. The type applies it to the object `X` and to `BaseQQ`, the base
  object of the library.
- `scheme::id`, `scheme::compose`, `scheme::apply` and `scheme::dimension`
  are the operations of the library.

The package depends on the standard library under the alias `std`. Generate
the library's package root first, as
[using the standard library](stdlib.md#using-the-standard-library) describes:

```sh
python3 scripts/build_stdlib_package.py
target/debug/vastitas build --manifest-path examples/packages/stdlib-geometry/Vastitas.toml -o target/stdlib-geometry
./target/stdlib-geometry
```

The program prints `42`, the sum of the two dimensions. The rules of identity
are those of the core: `p` is a point of `X`, and no operation accepts it as
a point of `Y`.
[The standard geometry library](../indexed-source.md#the-standard-geometry-library)
lists the declarations of both modules.

## The core syntax in a package

A program can write the core syntax and the names of the library side by
side. The manifest of the library's geometry package holds an
[*export*](../appendix/glossary.md#export): a table that maps each form of
the core syntax to a declaration of the library.
[`examples/packages/geometry-compat/main.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/packages/geometry-compat/main.vast)
depends on the standard library and uses both spellings:

```vast
{{#include ../../examples/packages/geometry-compat/main.vast}}
```

`Point<Y, Base(QQ)>` and `scheme::Point<Y, scheme::BaseQQ>` are the same
type here, so `q` and `r` are points of one type. `Affine(QQ, n)` and
`origin(X)` are calls of the library's operations.

```sh
target/debug/vastitas build --manifest-path examples/packages/geometry-compat/Vastitas.toml -o target/geometry-compat
./target/geometry-compat
```

The program prints `42`.

A flat program uses the built-in core, as the first sections of this chapter
do. So does a package, until its program has an indexed declaration or one
of the other declarations that
[Geometry compatibility exports](../packages.md#geometry-compatibility-exports)
lists. Such a program needs exactly one export among its packages to write
the core syntax.
[Core geometry syntax](../indexed-source.md#core-geometry-syntax) gives the
meaning of each form under an export.

<a id="declaring-an-indexed-profile"></a>The library has no special rights.
It declares its markers, objects, types and operations with indexed
declarations, and any package can do the same. The next chapter,
[Defining an indexed profile](indexed-profile.md), writes such declarations.

> **What is checked.** The checker compares the identities of objects and
> never their dimensions. It rejects a program before the compiler generates
> code, and it erases the identities only afterwards: at run time an object
> is its dimension. In a package, the checker resolves the declarations of
> the library and the entries of its export itself. The
> [proofs](../internals/indexed-checker.md#acceptance-and-proof-scope) cover
> the program that the checker hands to code generation: it is well typed,
> and each of its functions evaluates to a value of its declared type. They
> do not cover that this program computes what the source describes, or
> that the executable does. Tests cover the diagnostics and native
> execution.

## See also

- [Geometric types](../language/geometric-types.md): the types and
  operations of the geometric core, with
  [Object identity](../language/geometric-types.md#object-identity) and
  [Existential packages](../language/geometric-types.md#existential-packages).
- [Pack expressions](../language/expressions.md#pack-expressions) and
  [`unpack` statements](../language/statements.md#unpack-statements): both
  forms of each.
- [Indexed types](../language/types.md#indexed-types): types that apply a
  declared family.
- [The standard geometry library](../indexed-source.md#the-standard-geometry-library):
  the declarations of `std::geometry::scheme` and `std::geometry::smooth`.
- [Core geometry syntax](../indexed-source.md#core-geometry-syntax) and
  [Geometry compatibility exports](../packages.md#geometry-compatibility-exports):
  the core syntax in a package.
- [The geometry library](https://github.com/MGYamada/Vastitas/blob/main/stdlib/src/geometry/README.md):
  the modules of the library and their sources.
