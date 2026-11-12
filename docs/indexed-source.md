# Indexed declarations

An **indexed declaration** is an [item](language/items.md) that begins with
`indexed`. Indexed declarations give a package
[objects](appendix/glossary.md#nominal-object) of its own, and types whose
arguments are those objects. A set of indexed declarations that defines
one geometric setting is an [indexed profile](appendix/glossary.md#profile).
Indexed declarations exist only in
[manifest mode](language/programs.md#manifest-mode).

This chapter gives the rules that all indexed declarations share, and the
kinds of declarations that every profile uses: markers, implementations,
classifications, global objects, families, existential packages and
primitives. For implementations, families and primitives it gives the forms
of one profile, the profile of
[descriptor objects](appendix/glossary.md#descriptor-object), which record
only a dimension. Three other chapters give the declarations of the other
profiles:

| Declarations | Chapter |
| --- | --- |
| Smooth affine objects, smooth maps, fibers, tapes, metrics and evidence | [Smooth affine declarations](language/smooth-declarations.md) |
| Presented affine objects, morphisms over a base, isomorphisms and Cartesian squares | [Presented affine declarations](affine-geometry.md) |
| Scalar bases and linear implementations | [Linear implementations](linalg/maps-and-gemm.md#linear-implementations) |

[Notation](language/notation.md) explains the Syntax blocks, and the
[glossary](appendix/glossary.md) defines the terms.

> **Syntax**
>
> ```text
> IndexedDeclaration -> MarkerDeclaration | DescriptorImplementation
>     | ClassificationDeclaration | GlobalDeclaration | FamilyDeclaration
>     | PackageDeclaration | PrimitiveDeclaration
>     | ScalarBaseImplementation | LinearImplementation
>     | SmoothDeclaration | AffineDeclaration
> ```

The word after `indexed` is the kind of the declaration:

| Kind | Declares | Syntax |
| --- | --- | --- |
| `marker` | A [marker](#markers) | `MarkerDeclaration` |
| `implementation` | An [implementation](#implementations) | `DescriptorImplementation` here, `ScalarBaseImplementation` and `LinearImplementation` in [Linear implementations](linalg/maps-and-gemm.md#linear-implementations), `SmoothImplementation` in [The smooth profile](language/smooth-declarations.md#the-smooth-profile), and a form of `AffineDeclaration` |
| `classification` | A [classification](#classifications) | `ClassificationDeclaration` |
| `global` | A [global object](#global-objects) | `GlobalDeclaration` |
| `family` | A [family](#families) of types | `FamilyDeclaration` here, `SmoothFamily` in [The smooth profile](language/smooth-declarations.md#the-smooth-profile), and a form of `AffineDeclaration` |
| `package` | The types of [existential packages](#existential-packages) | `PackageDeclaration` |
| `primitive` | A [primitive](#primitives) | `PrimitiveDeclaration` |
| `affine` | A smooth affine object or a presented affine object | `AffineSpaceDeclaration` in [Smooth affine objects](language/smooth-declarations.md#smooth-affine-objects), and a form of `AffineDeclaration` |
| `morphism` | A smooth map or a morphism over a base | `MorphismDeclaration` in [Smooth maps](language/smooth-declarations.md#smooth-maps) |
| `metric`, `evidence` | A metric, and evidence for a metric | `MetricDeclaration` and `EvidenceDeclaration` in [Smooth affine declarations](language/smooth-declarations.md#metrics) |
| `iso`, `cartesian` | An isomorphism and a Cartesian square of presented affine objects | Forms of `AffineDeclaration` |

`SmoothDeclaration` stands for the declarations of
[Smooth affine declarations](language/smooth-declarations.md), and
`AffineDeclaration` for the declarations that only
[Presented affine declarations](affine-geometry.md) has.

Rules:

- The word after `indexed` must be a kind of the table. Another word before
  the name of a declaration is an error (`E_TYPE`).
- [Names of items](language/items.md#names-of-items) and
  [Reserved names](language/lexical-structure.md#reserved-names) give the
  rules on the name of a declaration.
- The identity of an indexed declaration is its
  [owner](language/edit-authority.md#owners): its package, its module and its
  name. Two declarations are different declarations, even when their text is
  the same.
- The name of a declaration chooses nothing. A family named `Point` holds
  points only when its declaration says `point`.
- Each path in an indexed declaration must name an indexed declaration. So
  must each path of an [indexed type](language/types.md#indexed-types),
  apart from the name of a parameter or of a binding at an `object(…)`
  parameter. A path to another item, such as a function, is an error
  (`E_TYPE`). [Names and paths](language/names-and-paths.md) gives the rules
  of resolution and visibility.
- A program has a limit on the number of its indexed declarations, which
  [Appendix D](appendix/limits.md#indexed-declarations) gives. More
  declarations are an error (`E_LIMIT`).
- An indexed declaration grants no
  [edit authority](language/edit-authority.md).

[The package graph](packages.md#the-package-graph) says that the compiler
checks every declaration of a program, including an indexed declaration that
nothing uses.

The examples quote the module `geo` of
[`examples/packages/indexed/`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/indexed)
and the package
[`examples/packages/indexed-objects/`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/indexed-objects).
[A complete program](#a-complete-program) uses the module `geo`.

> **Implementation note.** The Lean kernel resolves every path of a
> declaration and checks every declaration itself. It trusts no owner,
> representation, capability or validity claim from the frontend.
> [The indexed checker](internals/indexed-checker.md) describes these checks
> and what is proved about them.

## Markers

> **Syntax**
>
> ```text
> MarkerDeclaration -> `indexed` `marker` IDENTIFIER `;`
> ```

`indexed marker K;` declares a **marker** `K`: a static name for the
coefficients of objects, such as the rational numbers. An implementation names
the marker of its objects, and the type of an object names it again.

Rules:

- A marker is not an object. A marker in the place of an object, as in
  `geo::Point<X, geo::QQ>`, is an error (`E_TYPE`).
- A marker is not a value. The name of a marker in an expression is an error
  (`E_TYPE`).

```vast
{{#include ../examples/packages/indexed/geo.vast:marker}}
```

## Implementations

> **Syntax**
>
> ```text
> DescriptorImplementation -> `indexed` `implementation` IDENTIFIER
>     `(` Path `,` `affine_descriptor` `)` `capabilities` `(` Capabilities? `)` `;`
> Capabilities -> Capability ( `,` Capability )* `,`?
> Capability -> `origin` | `dimension`
> ```

`indexed implementation I(K, r) capabilities(c₁, …);` declares an
**implementation** `I`: one kind of object over the marker `K`. Its
**representation** `r` says what an object of `I` holds. The representation
`affine_descriptor` gives
[descriptor objects](appendix/glossary.md#descriptor-object). A
**capability** names an operation that the objects of `I` support:

| Capability | Operation |
| --- | --- |
| `origin` | The origin of an object, through a [primitive](#primitives) with the binding `origin(…)` |
| `dimension` | The dimension of an object, through a primitive with the binding `dimension(…)` |

The other representations are `scalar_base(…)` and `linear_descriptor(…)` of
[Linear implementations](linalg/maps-and-gemm.md#linear-implementations),
`presented_affine(rational)` of
[The presented profile](affine-geometry.md#the-presented-profile) and
`smooth_affine` of
[The smooth profile](language/smooth-declarations.md#the-smooth-profile).

Rules:

- The path must name a marker (`E_TYPE`).
- The representation must be one of the five representations. Another word
  is an error (`E_TYPE`).
- A capability must be `origin` or `dimension`. Another word is an error
  (`E_TYPE`).
- The capability list must not name a capability twice (`E_TYPE`).
- An implementation has the capabilities of its own declaration, and no
  others. A classification adds none.

In the module `geo`, the objects of `Grid` support both operations:

```vast
{{#include ../examples/packages/indexed/geo.vast:implementation}}
```

In `indexed-objects`, the objects of `Plain` support neither:

```vast
{{#include ../examples/packages/indexed-objects/shapes.vast:implementations}}
```

## Classifications

> **Syntax**
>
> ```text
> ClassificationDeclaration -> `indexed` `classification` IDENTIFIER `{`
>     `parents` `(` Paths? `)` `;` `domain` `(` Paths? `)` `;` `}` `;`
> Paths -> Path ( `,` Path )* `,`?
> ```

`indexed classification C { parents(P₁, …); domain(I₁, …); };` declares a
**classification** `C`: a finite set of implementations under one name. The
**domain** of `C` is the list `I₁, …`. The domain of an implementation is that
implementation alone. Each `Pᵢ` is a parent of `C`: a classification whose
domain contains the domain of `C`.

A classification stands for the objects of all its implementations. It serves
in [object types](#object-types), in the parameters of
[families](#families) and in the bindings of [primitives](#primitives).

Rules:

- Each path of `domain` must name an implementation, and the domain must
  not name an implementation twice (`E_TYPE`).
- The domain must not be empty (`E_TYPE`).
- Each path of `parents` must name a classification, and `parents` must not
  name a classification twice (`E_TYPE`).
- The domain of each parent must contain every implementation of the domain
  of `C` (`E_TYPE`).
- The parents must not form a cycle. A classification that reaches itself
  through `parents` is an error (`E_TYPE`).
- The length of a domain has a limit, which
  [Appendix D](appendix/limits.md#indexed-declarations) gives (`E_TYPE`).
- The implementations of one domain may have different markers.
- `parents` states a relation that the compiler checks. It gives `C` no
  implementation and no capability. The other rules of this chapter compare
  domains and never read the parents.

In `indexed-objects`, `Measured` has the parent `Shape`, whose domain contains
`Grid`:

```vast
{{#include ../examples/packages/indexed-objects/shapes.vast:classifications}}
```

## Global objects

> **Syntax**
>
> ```text
> GlobalDeclaration -> `indexed` `global` IDENTIFIER `(` Path `)` `;`
> ```

`indexed global G(I);` declares a **global object** `G`: one object of the
implementation `I`. Every module that sees the declaration names the same
object. A type names `G` by a path, as in `geo::Point<X, geo::Base>`.

Rules:

- The path must name an implementation (`E_TYPE`).
  [Smooth affine objects](language/smooth-declarations.md#smooth-affine-objects)
  and [Presented affine objects](affine-geometry.md#presented-affine-objects)
  say how the objects of their implementations are declared.
- Each declaration is one object. Two global objects are different objects,
  even when they have the same implementation.
- The [object type](#object-types) of `G` is `Object<I, K>`, where `K` is the
  marker of `I`.
- A global object of an `affine_descriptor` implementation has the
  dimension 0.
- The name of a global object is not a value. In an expression it is an error
  (`E_TYPE`). A [primitive](#primitives) with the binding `global(G)` gives
  the object.

```vast
{{#include ../examples/packages/indexed/geo.vast:global}}
```

## Object types

The type `Object<D, K>` of
[Indexed types](language/types.md#indexed-types) is an **object type**. `D`
names a classification or an implementation, and `K` names a marker. The
implementations of `Object<D, K>` are the implementations in the domain of
`D` whose marker is `K`. An object type **lies within** a second object type
when both name the same marker and every implementation of the first is an
implementation of the second. It lies within a classification or an
implementation `C` when all its implementations are in the domain of `C`.

An expression that denotes an object has one object type:

| Expression | Object type |
| --- | --- |
| A parameter, or a `let` binding with an annotation | The type that the program writes |
| A `let` binding without an annotation | The object type of its value |
| A call of a function | The result type of the function |
| A global object `G` of the implementation `I` over `K` | `Object<I, K>` |
| A call of a primitive with the binding `descriptor(I)` | `Object<I, K>` |
| The witness that an `unpack` statement binds | The witness type of the [existential package](#existential-packages) |

The object type belongs to the expression. Two bindings of one object may
have different object types. A diagnostic writes the object type
`Object<D, K>` as `D<K>`.

Rules:

- `D` must name a classification or an implementation, and `K` must name a
  marker (`E_TYPE`).
- An object type must have at least one implementation (`E_TYPE`).
- Where a parameter, an annotation or a result type is an object type, the
  object type of the value must lie within it. Another object type is an
  error (`E_TYPE`).
- A binding with an annotation has the object type of the annotation, even
  when the object type of its value is narrower. The binding and the value
  are the same object.
- The two branches of an `if` expression must have one object type.
  Otherwise it is an error (`E_TYPE`). Under an annotation, the object type
  of each branch must lie within the annotation instead.

In `indexed-objects`, `shapes::grid` gives an object of type
`Object<shapes::Grid, shapes::QQ>`. This type lies within the parameter types
of both `measure` and `hide`:

```vast
{{#include ../examples/packages/indexed-objects/main.vast:object-types}}
```

The executable prints `42`. The witness `Y` has the object type
`Object<shapes::Shape, shapes::QQ>`, so `measure(Y)` is an error. In the next
program the annotation gives `Y` an object type that has the implementation
`Plain`, which lacks the capability `dimension`:

```vast
{{#include ../examples/reject/packages/lost-capability/main.vast}}
```

```text
{{#include ../examples/reject/packages/lost-capability.stderr}}
```

## Families

> **Syntax**
>
> ```text
> FamilyDeclaration -> `indexed` `family` IDENTIFIER `(` Parameters? `)`
>     `=` FamilyRepresentation `constraints` `(` Constraints? `)` `;`
> FamilyRepresentation -> `token` | `point` | `morphism`
> Parameters -> Parameter ( `,` Parameter )* `,`?
> Parameter -> `domain` | `marker` | `natural` | `object` `(` Path `)`
> Constraints -> Constraint ( `,` Constraint )* `,`?
> Constraint -> `canonical` `(` INTEGER_LITERAL `)`
>     | ConstraintKind `(` INTEGER_LITERAL `,` INTEGER_LITERAL `)`
> ConstraintKind -> `same_object` | `same_base` | `over` | `structural`
> ```

`indexed family F(p₁, …, pₙ) = r constraints(c₁, …);` declares a **family**
`F`: a type former with `n` parameters. An
[indexed type](language/types.md#indexed-types) `F<a₁, …, aₙ>` applies `F` to
one argument for each parameter:

| Parameter | Argument |
| --- | --- |
| `domain` | A path that names a classification or an implementation |
| `marker` | A path that names a marker |
| `natural` | An integer literal |
| `object(C)` | An object whose object type lies within `C`. It is the name of a parameter or of a binding in scope, or a path that names a declared object: a global object, or an object of an `indexed affine` declaration |

A constraint restricts the arguments of the family. It names parameters by
their positions, which count from 0:

| Constraint | Holds when |
| --- | --- |
| `same_object(i, j)` | The arguments `i` and `j` are the same object |
| `same_base(i, j)` | The objects `i` and `j` have the same marker |
| `over(i, j)` | The object `i` has the marker that the argument `j` names |

`structural(i, j)` is a constraint of
[The presented profile](affine-geometry.md#the-presented-profile), and
`canonical(i)` is a
constraint of
[The smooth profile](language/smooth-declarations.md#the-smooth-profile).

The representation `r` says which values the types of the family have:

| Representation | Values of the type |
| --- | --- |
| `token` | None. No primitive builds a value of a `token` family |
| `point` | `F<X, S>` holds the points of the object `X` with the [test object](appendix/glossary.md#test-object) `S` |
| `morphism` | `F<X, Y>` holds the morphisms from the object `X` to the object `Y` |

The [primitives](#primitives) build and use the values of `point` and
`morphism` families. The representations `smooth`, `cotangent`, `tangent`,
`tape` and `metric_form` are in
[The smooth profile](language/smooth-declarations.md#the-smooth-profile), and
`relative` is in
[The presented profile](affine-geometry.md#the-presented-profile).

Rules:

- The representation must be one of the nine representations. Another word
  is an error (`E_TYPE`). So is another word for a parameter or for a
  constraint.
- The path of `object(C)` must name a classification or an implementation
  (`E_TYPE`).
- A position must be an integer literal (`E_PARSE`), and it must fit in 32
  bits (`E_LIMIT`).
- Each position of `same_object` and `same_base`, and the first position of
  `over`, must be the position of an `object(…)` parameter. The second
  position of `over` must be the position of a `marker` parameter. Another
  position is an error (`E_TYPE`).
- A `point` or `morphism` family must have exactly two parameters, both
  `object(…)`, and the constraint `same_base(0, 1)`. Otherwise it is an error
  (`E_TYPE`). The family may have further constraints.
- Every implementation in the domains of the two parameters of a `point` or
  `morphism` family must have the representation `affine_descriptor`
  (`E_TYPE`).
- The number of parameters has a limit, which
  [Appendix D](appendix/limits.md#indexed-declarations) gives (`E_TYPE`).

The module `geo` declares one family of each of the two representations with
values:

```vast
{{#include ../examples/packages/indexed/geo.vast:families}}
```

### Indexed types of a family

An indexed type `F<a₁, …, aₙ>` is valid when its arguments fit the parameters
and the constraints of `F`.

Rules:

- The path of the type must name a family, or a package declaration as
  [Existential packages](#existential-packages) says (`E_TYPE`).
- The type must have one argument for each parameter (`E_TYPE`).
- Each argument must have the form that the table of parameters gives
  (`E_TYPE`).
- A name that names neither a binding in scope nor a declaration is an error
  (`E_NAME`). Only an `object(C)` parameter takes a binding, so the name of a
  binding at a `domain` or `marker` parameter is such a name.
- Every constraint of the family must hold for the arguments (`E_TYPE`).
- A `natural` argument may be an integer of any size. It is part of the type
  only: no value holds it at run time, and it is not a
  [dispatch key](appendix/glossary.md#dispatch-key).
- Two indexed types are the same type when they apply the same family to the
  same arguments. [Object identity](#object-identity) says when two objects
  are the same.
- An indexed type must not be an input or a result of a function type.
  [Function types](language/types.md#function-types) gives the code of this
  error.
- Before `<`, the bare names `Point`, `Morphism` and `Pointed` are types of
  the [geometric core](language/geometric-types.md), as
  [Indexed types](language/types.md#indexed-types) says. A type applies a
  family of such a name through a path with `::`. Examples are
  `geo::Point<X, geo::Base>`, and `self::Point<X, Base>` in the declaring
  module.

`indexed-objects` declares a `token` family. The type of `label` applies it to
an object, a marker and a number:

```vast
{{#include ../examples/packages/indexed-objects/shapes.vast:token}}
```

```vast
{{#include ../examples/packages/indexed-objects/main.vast:label}}
```

## Existential packages

> **Syntax**
>
> ```text
> PackageDeclaration -> `indexed` `package` IDENTIFIER `{` PackageCase* `}` `;`
> PackageCase -> `case` `(` Path `,` Path `)` `{` PackageField* `}`
> PackageField -> Path `(` BoundIndices? `)` `;`
> BoundIndices -> BoundIndex ( `,` BoundIndex )* `,`?
> BoundIndex -> `witness` | INTEGER_LITERAL | `global` `(` Path `)`
>     | `domain` `(` Path `)` | `marker` `(` Path `)`
> ```

`indexed package P { case(D, K) { F₁(…); …; Fₙ(…); } … };` declares the types
of [existential packages](appendix/glossary.md#existential-package). Each
**case** declares one type, `P<D, K>`. A value of `P<D, K>` hides one object,
its [witness](appendix/glossary.md#witness), together with one value for each
**field** of the case. The **witness type** of the case is the object type
`Object<D, K>`. A field `F(b₁, …, bₘ)` has the type that applies the family
`F` to its **bound indices**:

| Bound index | Argument of the family |
| --- | --- |
| `witness` | The witness |
| `global(G)` | The declared object `G`: a global object, or an object of an `indexed affine` declaration |
| `domain(C)` | The classification or implementation `C` |
| `marker(K)` | The marker `K` |
| An integer literal | That number |

Rules:

- A declaration must have at least one case (`E_TYPE`).
- The witness type of a case must be an object type by the rules of
  [Object types](#object-types) (`E_TYPE`).
- Two cases must not have the same witness type, that is the same `D` and the
  same `K` (`E_TYPE`). Witness types that name different declarations are
  different, even when they have the same implementations.
- The path of a field must name a family (`E_TYPE`).
- The bound indices of a field must be arguments of its family, by the rules
  of [Indexed types of a family](#indexed-types-of-a-family), for every
  object of the witness type (`E_TYPE`). In particular, the witness type must
  lie within `C` where `witness` is the argument of an `object(C)` parameter.
- A bound index must have one of the five forms. Another word before `(` is
  an error (`E_TYPE`).
- A case may have no field, and a field may leave out `witness`.
- The numbers of cases and of fields have limits, which
  [Appendix D](appendix/limits.md#indexed-declarations) gives (`E_TYPE`).
- A type `P<D, K>` must name the `D` and the `K` of one case (`E_TYPE`).

The module `geo` declares one case, whose field is a point of the witness
with the test object `Base`:

```vast
{{#include ../examples/packages/indexed/geo.vast:package}}
```

`indexed-objects` declares two cases without fields. Their witness types are
different, although both have the implementation `Grid`:

```vast
{{#include ../examples/packages/indexed-objects/shapes.vast:package}}
```

### Packing

`pack P<D, K> { witness: w, fields: [e₁, …, eₙ] }` is a
[pack expression](language/expressions.md#pack-expressions). Its value is an
existential package of type `P<D, K>` that hides the object `w` together with
the values of the fields.

Rules:

- The type must be the type of one case of a package declaration (`E_TYPE`).
- `w` must be an object whose object type lies within the witness type
  (`E_TYPE`).
- The expression must give one value for each field, in the order of the
  case. The value of field `i` must have the type of that field with `w` as
  the witness. Other fields are an error (`E_ENDPOINT`). They include a
  missing field, an extra field and a field over another object.

In this program the field is a point of `Y`, and the witness is `X`:

```vast
{{#include ../examples/reject/packages/other-witness/main.vast}}
```

```text
{{#include ../examples/reject/packages/other-witness.stderr}}
```

### Opening

`unpack e as { witness: Y, fields: [x₁, …, xₙ] };` is an
[`unpack` statement](language/statements.md#unpack-statements). It binds `Y`
to the witness of `e` and each `xᵢ` to the value of field `i`.

Rules:

- The statement must name one binding for each field of the case
  (`E_ARITY`).
- The object type of `Y` is the witness type of the case, even when the
  object that `pack` hid has a narrower object type.
- The type of `xᵢ` is the type of field `i` with `Y` as the witness.
- [Existential packages](language/geometric-types.md#existential-packages)
  gives the identity of `Y` and the rules on values that leave the block of
  the statement. Those rules hold for every field, including a field of a
  `token` family.
- `unpack e as { scheme: Y, point: x };` is
  `unpack e as { witness: Y, fields: [x] };`. In manifest mode it opens every
  existential package that has one field.

This program opens one existential package twice. The two witnesses are
different objects:

```vast
{{#include ../examples/reject/packages/second-opening/main.vast}}
```

```text
{{#include ../examples/reject/packages/second-opening.stderr}}
```

## Primitives

> **Syntax**
>
> ```text
> PrimitiveDeclaration -> `indexed` `primitive` IDENTIFIER `=` PrimitiveBinding `;`
> PrimitiveBinding -> DescriptorBinding | SmoothBinding | RelativeBinding
> DescriptorBinding -> `descriptor` `(` Path `)`
>     | `global` `(` Path `)`
>     | `origin` `(` `(` Path `,` Path `)` `,` Path `,` Path `)`
>     | `identity` `(` `(` Path `,` Path `)` `,` Path `)`
>     | `dimension` `(` `(` Path `,` Path `)` `)`
>     | `compose` `(` Path `)`
>     | `apply` `(` Path `,` Path `)`
> ```

`indexed primitive p = b;` declares a **primitive** `p`: a function whose
operands and result `b` fixes. `b` is the **primitive binding** of `p`. Where
the text names a primitive, it calls `b` the binding of the primitive. The
primitive bindings form a closed set. A program declares no operation of its
own, and a primitive binding names no native code. `SmoothBinding` gives the
bindings of
[Smooth affine declarations](language/smooth-declarations.md#smooth-map-primitives),
and `RelativeBinding` gives the bindings of
[Morphism primitives](affine-geometry.md#morphism-primitives).

In the table, `I` is an implementation over the marker `K`, and `G` and `B`
are global objects. `(D, K)` stands for the object type `Object<D, K>`. `P` is
a `point` family, and `M` is a `morphism` family.

| Binding | Operands | Result | Value |
| --- | --- | --- | --- |
| `descriptor(I)` | `n: Nat` | An object of type `Object<I, K>` | A fresh descriptor object of dimension `n` |
| `global(G)` | None | The object `G` | The global object `G` |
| `origin((D, K), P, B)` | An object `X` | `P<X, B>` | The origin of `X` |
| `identity((D, K), M)` | An object `X` | `M<X, X>` | The identity morphism of `X` |
| `dimension((D, K))` | An object `X` | `Nat` | The dimension of `X` |
| `compose(M)` | `g: M<Y, Z>`, `f: M<X, Y>` | `M<X, Z>` | `g` after `f` |
| `apply(M, P)` | `f: M<X, Y>`, `p: P<X, S>` | `P<Y, S>` | The image of `p` under `f` |

Rules:

- The word after `=` must begin a binding of `PrimitiveBinding`. Another
  word before `(` is an error (`E_TYPE`).
- The implementation of `descriptor(I)` must have the representation
  `affine_descriptor` (`E_TYPE`).
- The path of `global(G)` must name a global object of an implementation
  with the representation `affine_descriptor` (`E_TYPE`).
- `(D, K)` must be an object type by the rules of
  [Object types](#object-types) (`E_TYPE`).
- Every implementation of `Object<D, K>` must have the capability `origin`
  for the binding `origin`, and the capability `dimension` for the binding
  `dimension` (`E_TYPE`).
- `P` must name a family with the representation `point`, and `M` a family
  with the representation `morphism` (`E_TYPE`).
- `P<X, B>` of the binding `origin` must be an indexed type by the rules of
  [Indexed types of a family](#indexed-types-of-a-family), for every object
  `X` of type `Object<D, K>` (`E_TYPE`). In particular, `B` must name a
  global object over the marker `K`.
- `M<X, X>` of the binding `identity` must be an indexed type by the same
  rules, for every object `X` of type `Object<D, K>` (`E_TYPE`).

The module `geo` declares one primitive for each binding:

```vast
{{#include ../examples/packages/indexed/geo.vast:primitives}}
```

In this package the domain of `Shape` has the implementation `Plain`, which
lacks the capability `dimension`. The compiler reports the binding at its
declaration:

```vast
{{#include ../examples/reject/packages/missing-capability/main.vast}}
```

```text
{{#include ../examples/reject/packages/missing-capability.stderr}}
```

### Calls of primitives

A program calls a primitive by its path, with the syntax of a
[call expression](language/expressions.md#call-expressions). The table of
bindings gives the operands and the result of the call.

Rules:

- The name of a primitive is not a value. Using it as one is an error
  (`E_TYPE`).
- A call must have the number of operands that the table gives (`E_ARITY`).
- An operand must have the kind that the table gives: a number, an object or
  a value of a family. Another kind is an error (`E_TYPE`).
- An integer literal as the operand of a `descriptor` primitive has the type
  `Nat`.
- The object type of the operand `X` must lie within `Object<D, K>`.
  Otherwise the call is an error (`E_ENDPOINT`).
- The operands of `compose` and `apply` must be values of the families `M`
  and `P`, and their objects must agree as the table says. Otherwise the call
  is an error (`E_ENDPOINT`).
  [Operations](language/geometric-types.md#operations) says what an
  `E_ENDPOINT` diagnostic names.
- The result type of a call must be an indexed type by the rules of
  [Indexed types of a family](#indexed-types-of-a-family). Otherwise the call
  is an error (`E_ENDPOINT`), even when the declaration of the primitive is
  valid.
- A call of a name that is an indexed declaration and not a primitive is an
  error (`E_TYPE`).

[A complete program](#a-complete-program) calls five of the seven primitives
of the module `geo`.

> **Implementation note.** After the check, the kernel erases
> implementations, classifications and markers. An object is a descriptor of
> its dimension at run time, and two objects with equal descriptors are still
> different objects for the checker.

## Object identity

Every object has a
[nominal identity](appendix/glossary.md#nominal-identity).
[Object identity](language/geometric-types.md#object-identity) gives the
rules on bindings, function results and `if` expressions, and they hold for
the objects of every indexed profile.

Rules:

- Each call of a primitive with the binding `descriptor(I)` creates an object
  with a fresh identity.
- A global object is one object. Every path that names it and every call of a
  primitive with the binding `global(G)` denote that object.
- Equal implementations, markers and dimensions never make two objects the
  same.

## Core geometry syntax

The [geometric core](language/geometric-types.md) has built-in types and
operations, such as `Point<X, Base(QQ)>` and `origin(X)`. In manifest mode an
[export](packages.md#geometry-compatibility-exports), the `[geometry_compat]`
table of a manifest, maps each of them to an indexed declaration.
[Geometry compatibility exports](packages.md#geometry-compatibility-exports)
says which programs need an export, and where the compiler reports an invalid
one. This section gives the entries of the table and the meaning of the core
syntax.

### Entries of an export

The table has five entries of its own and two subtables,
`[geometry_compat.scheme]` for the
[setting](appendix/glossary.md#setting) `Scheme` and
`[geometry_compat.smooth]` for the setting `CInfScheme`. Each subtable has
the same eight entries. Every entry is a path. In the second column, the name
of an entry stands for the declaration that the entry names, and the object
type of a setting is `Object<domain, marker>`.

| Entry | Names |
| --- | --- |
| `point` | A family with the representation `point` and the one constraint `same_base(0, 1)` |
| `morphism` | A family with the representation `morphism` and the one constraint `same_base(0, 1)` |
| `pointed` | A package declaration. For each setting it has a case with the object type of the setting as its witness type and the one field `point(witness, global(base_object))` |
| `compose` | A primitive with the binding `compose(morphism)` |
| `apply` | A primitive with the binding `apply(morphism, point)` |
| `domain` | A classification |
| `marker` | A marker |
| `base_object` | A global object whose object type lies within the object type of the setting |
| `affine` | A primitive with the binding `descriptor(I)`, where `Object<I, marker>` lies within the object type of the setting |
| `base` | A primitive with the binding `global(base_object)` |
| `origin` | A primitive with the binding `origin((domain, marker), point, base_object)` |
| `identity` | A primitive with the binding `identity((domain, marker), morphism)` |
| `dimension` | A primitive with the binding `dimension((domain, marker))` |

Rules:

- The table must have every entry of this section and no other entry.
  [Manifests](packages.md#manifests) gives the error for a missing key and
  for an unknown key.
- Each entry must name a declaration as the table says. The object type of
  each setting must be an object type by the rules of
  [Object types](#object-types), and `point` and `morphism` must take the
  objects of both settings as arguments. An export that breaks this rule is
  invalid, and
  [Geometry compatibility exports](packages.md#geometry-compatibility-exports)
  gives its error.
- The entries `scheme.marker` and `smooth.marker` must name different
  markers. Otherwise the export is invalid.
- An entry may name a declaration that is private to the root module of the
  exporting package. The core syntax then reaches that declaration from
  every module of the program.
- An export declares nothing, and it grants no
  [edit authority](language/edit-authority.md).

### Meaning of the core syntax

With one export in the package graph, the core syntax has this meaning in
every module of the program. The setting of an object is the setting whose
object type the object type of the object lies within.

| Core syntax | Meaning |
| --- | --- |
| `Scheme`, `CInfScheme` | The object type of the setting |
| `Base(QQ)`, `Base(CInfReal)` as an argument of a core type | The global object `base_object` of the setting |
| `Point<X, S>` | `point<X, S>` |
| `Morphism<X, Y>` | `morphism<X, Y>` |
| `Pointed<Scheme, QQ>`, `Pointed<CInfScheme, CInfReal>` | `pointed<domain, marker>` of the setting |
| `Affine(QQ, n)`, `Affine(CInfReal, n)` | A call of `affine` of the setting |
| `Base(QQ)`, `Base(CInfReal)` in an expression | A call of `base` of the setting |
| `origin(X)`, `id(X)`, `dimension(X)` | A call of `origin`, `identity` or `dimension` of the setting of `X` |
| `compose(g, f)`, `apply(f, p)` | A call of `compose` or `apply` |
| `pack { scheme: X, point: p }` | `pack pointed<domain, marker> { witness: X, fields: [p] }` for the setting of `X` |

Rules:

- The rules of [Geometric types](language/geometric-types.md) hold for the
  core syntax with this meaning.
- A type in the core syntax is the same type as the indexed type that it
  means, and a call is the same call as the call of the primitive. A program
  may use both spellings for one value.
- An object whose object type lies within the object type of neither setting
  has no setting. A core operation on such an object, and a `pack` of the
  core with it, are errors (`E_TYPE`).
- A bare name that the current module declares or imports wins over the core
  operation of that name. For example, `dimension(X)` calls an imported
  primitive `dimension`.
- A program may write `unpack e as { scheme: X, point: p };` without an
  export, as [Opening](#opening) says.

The package
[`examples/packages/geometry-compat/`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/geometry-compat)
depends on the standard library, whose geometry package holds an export:

```toml
{{#include ../examples/packages/geometry-compat/Vastitas.toml}}
```

```vast
{{#include ../examples/packages/geometry-compat/main.vast}}
```

`p`, `q` and `r` are points of one type, written in both spellings. The
executable prints `42`.

> **Implementation note.** The kernel resolves the paths of every export and
> checks each entry against the declarations themselves. A call in the core
> syntax compiles to the code of the primitive that it means. The export adds
> no operation to the generated program.

## The standard geometry library

The geometry package of the standard library declares one profile of
descriptor objects for each setting of the geometric core.
`std::geometry::scheme` and `std::geometry::smooth` are the modules of the
two profiles:

| Declaration | `std::geometry::scheme` | `std::geometry::smooth` |
| --- | --- | --- |
| Marker | `QQ` | `CInfReal` |
| Implementation | `GridQQ` | `GridSmooth` |
| Classification | `Scheme` | `CInfScheme` |
| Global object | `BaseQQ` | `BaseSmooth` |
| Primitives | `Affine`, `base`, `origin`, `id`, `dimension` | `Affine`, `base`, `origin`, `id`, `dimension` |

Both modules also export the families `Point` and `Morphism`, the package
declaration `Pointed` with one case for each setting, and the primitives
`compose` and `apply`. The two modules share these five declarations. Each
module has a function `pointed(n)`, which packs a fresh object of dimension
`n` with its origin. The
[manifest](https://github.com/MGYamada/Vastitas/blob/main/stdlib/src/geometry/Vastitas.toml)
of the package holds the [export](#core-geometry-syntax) that maps the core
syntax to these declarations.

```vast
{{#include ../examples/packages/stdlib-geometry/main.vast}}
```

The executable prints `42`.

## A complete program

The root module of `examples/packages/indexed/` uses the declarations of its
module `geo` through paths:

```vast
{{#include ../examples/packages/indexed/main.vast}}
```

```sh
vastitas check --manifest-path examples/packages/indexed/Vastitas.toml
vastitas build --manifest-path examples/packages/indexed/Vastitas.toml -o target/indexed-demo
./target/indexed-demo
```

The executable prints `42`. `make` hides an object of dimension 41 together
with its origin. `main` opens the existential package, applies the identity
morphism of the witness to the point, and adds 1 to the dimension.

## Scope of the descriptor profile

The declarations of this chapter give descriptor objects. Their points are
origins and the images of origins, and their morphisms are identities and
composites of identities. The declarations give no coordinates, no map with a
formula, no array and no storage.
[Smooth affine declarations](language/smooth-declarations.md) and
[Presented affine declarations](affine-geometry.md) declare objects with
coordinates and maps between them, and
[Numerical maps](linalg/maps-and-gemm.md) gives the storage of linear maps.
