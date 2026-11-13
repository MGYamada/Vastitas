# Presented affine declarations

This chapter defines the declarations of presented affine geometry over the
rational numbers. They declare presented affine objects and their bases,
morphisms over a base, isomorphisms, fiber products, Cartesian squares and
principal opens, and the primitive bindings that act on morphisms. A
**presented affine object** is the affine scheme
$\operatorname{Spec}\, \mathbb{Q}[g_1, \dots, g_n]/(r_1, \dots, r_m)$ that a
declaration presents by **coordinates** $g_i$ and polynomial **relations**
$r_j$.
The general rules of `indexed` declarations, such as visibility, names,
markers and classifications, are in
[indexed declarations](indexed-source.md).
[Notation](language/notation.md) explains the Syntax blocks, and the
[glossary](appendix/glossary.md) defines the terms.

The examples quote the tested package
[`examples/packages/affine-geometry/`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/affine-geometry),
whose executable prints `42`. Each rejected program is a package on the
profile of the standard library. It appears with the diagnostic that the
compiler prints for it.

> **Syntax**
>
> ```text
> AffineDeclaration -> PresentedImplementation | RelativeFamily
>     | PresentedObjectDeclaration | IsomorphismDeclaration
>     | CartesianDeclaration
> ```

Each alternative is one form of `IndexedDeclaration`, an
[item](language/items.md). `pub` before it makes it visible outside its
module. Three further forms of this chapter have their productions in other
chapters. A [morphism over a base](#morphisms-over-a-base) is a
`MorphismDeclaration`, which [Smooth maps](language/smooth-declarations.md#smooth-maps)
defines. A [primitive](#morphism-primitives) of this chapter is a
`PrimitiveDeclaration`, which [Primitives](indexed-source.md#primitives)
defines, with a `RelativeBinding`. `Affine(K, n)[…]`, another spelling of a
[presented affine object](#presented-affine-objects), is an
`AffineSpaceDeclaration`, which
[Smooth affine objects](language/smooth-declarations.md#smooth-affine-objects)
defines.

The relations and the images of this chapter are
[polynomial expressions](language/smooth-declarations.md#polynomial-expressions)
with rational coefficients. That section defines `Polynomial` and
`CoordinateName`, and its rules apply to every polynomial expression of this
chapter. [Smooth affine declarations](language/smooth-declarations.md) also
defines `Coordinates` and `ImageBindings`.
[Indexed declarations](indexed-source.md) defines `Capabilities`,
`Parameters` and `Constraints`.

The compiler reports an error of a declaration of this chapter at the
declaration. An error about an object that a path of the declaration names
has the place of that path. One such error is a base or a factor that is not
a presented affine object. Others are about a morphism over a base: a source
or a target that is not a presented affine object, and a base that is not on
the base chain of the source or of the target. The last is a source or a
target of `relative_coefficient` that is not a presented affine object. A
coordinate and a polynomial have no place of their own, so an error about
one of them has the place of its declaration.

## The presented profile

> **Syntax**
>
> ```text
> PresentedImplementation -> `indexed` `implementation` IDENTIFIER
>     `(` Path `,` `presented_affine` `(` `rational` `)` `)`
>     `capabilities` `(` Capabilities? `)` `;`
> RelativeFamily -> `indexed` `family` IDENTIFIER `(` Parameters? `)`
>     `=` `relative` `constraints` `(` Constraints? `)` `;`
> ```

An implementation with the `presented_affine(rational)` representation backs
the presented affine objects. `rational` names the field of their
coefficients, the rational numbers. A classification whose domain lists such
an implementation, such as `AffineScheme` below, is the classification over
which a relative family ranges. A **relative family** is a family with the
`relative` representation. The indexed type `Over<X, Y, S>` of such a family
is the type of the [morphisms](#morphisms-over-a-base) from `X` to `Y` over
the base `S`.

The constraint `structural(i, j)` holds for an indexed type when its
arguments `i` and `j` are presented affine objects and argument `j` lies on
the [base chain](#presented-affine-objects) of argument `i`. Every object
lies on its own base chain. The constraint compares declarations, never
markers or presentations. Only a declared object satisfies it: a parameter,
and an object that a function body creates or opens, never do. The two
constraints of a relative family say that the source and the target both lie
over the base.

The standard library declares one presented profile.
`std::geometry::scheme::affine` declares the implementation `AffineQQ`, the
classification `AffineScheme`, the family `Over` and the primitives `compose`
and `same`. It declares three objects: `SpecQQ` is `spec[]`, `Line` is
`spec[t] over SpecQQ`, and `DualNumbers` is
`spec[e] relations(e^2) over SpecQQ`. A program may use these declarations or
declare a profile of its own. Each declaration is a distinct object or family,
so a program's own `spec[t] over SpecQQ` is not the library's `Line`.

Rules:

- A `presented_affine` implementation must list no capabilities. Otherwise it
  is an error (`E_TYPE`).
- The field must be `rational`. Any other word is an error (`E_TYPE`).
- An `indexed global` under a `presented_affine` implementation is an error
  (`E_TYPE`). Every presented affine object is an `indexed affine`
  declaration.
- A relative family must have exactly three parameters, each of the form
  `object(C)`, and exactly the constraints
  `structural(0, 2), structural(1, 2)`, in this order. Otherwise it is an
  error (`E_TYPE`).
- Every implementation in the domain of each `C` must have the
  `presented_affine` representation. Otherwise it is an error (`E_TYPE`). In particular, a
  relative family never ranges over descriptor objects or smooth affine
  objects.
- A presented affine object never indexes a family with the `point` or
  `morphism` representation: [Families](indexed-source.md#families) admits
  only descriptor objects there.
- Both positions of `structural(i, j)` must be the positions of `object(…)`
  parameters. Otherwise it is an error (`E_TYPE`). A family with the `token` representation may
  state the constraint.
- A type whose arguments fail a `structural` constraint is an error
  (`E_TYPE`).

> **Implementation note.** The driver sends a package graph that holds a
> declaration of this chapter through wire protocol 9, as
> [protocol selection](protocol.md#protocol-selection) says. This includes
> every program that depends on the geometry package of the standard library.
> An earlier protocol rejects each form of this chapter (`E_PROTOCOL`), as
> [the wire forms](protocol.md#protocol-9-algebraic-affine-forms) say. No
> source program reaches that error.

Example, from
[`profile.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/packages/affine-geometry/src/profile.vast):

```vast
{{#include ../examples/packages/affine-geometry/src/profile.vast:profile}}
```

In the following program on the profile of the standard library, `Curve`
lies over `Line` and `DualNumbers` does not:

```vast
{{#include ../examples/reject/packages/affine-off-chain/main.vast:declarations}}
```

```text
{{#include ../examples/reject/packages/affine-off-chain.stderr}}
```

## Presented affine objects

> **Syntax**
>
> ```text
> PresentedObjectDeclaration -> `indexed` `affine` IDENTIFIER `(` Path `)`
>     `=` PresentedObject `;`
> PresentedObject -> Spectrum | FiberProduct | PrincipalOpen
> Spectrum -> `spec` `[` Coordinates? `]` ( `relations` `(` Relations? `)` )?
>     ( `over` Path ( `by` `(` ImageBindings? `)` )? )?
> Relations -> Polynomial ( `,` Polynomial )* `,`?
> ```

`indexed affine X(Impl) = spec[g₁, …, gₙ] relations(r₁, …, rₘ) over B by(b₁ -> p₁, …)`
declares a presented affine object under the implementation `Impl`. Its
coordinates $g_1, \dots, g_n$ and its relations $r_1, \dots, r_m$ present
its **coordinate ring**
$A = \mathbb{Q}[g_1, \dots, g_n]/(r_1, \dots, r_m)$, and the object is
$\operatorname{Spec}\, A$. Each relation is a polynomial expression in the
coordinates. A [fiber product](#fiber-products) and a
[principal open](#principal-opens) are presented affine objects whose
coordinates and relations the compiler derives.

`over B` names the **base** of the object, which is another presented affine
object. `by(…)` gives the **structure map** of `X`, the morphism $X \to B$.
For each coordinate $b$ of `B` it gives the image of $b$ in the coordinate
ring of `X`, as a polynomial expression in the coordinates of `X`. An object
without `over` has no base. The **base chain** of an object is the object,
its base, the base of that base, and so on. It ends at an object without a
base.

Each declaration is one object with its own
[nominal identity](appendix/glossary.md#nominal-identity). Two declarations
with the same presentation are different objects, and no rule identifies
them. An [isomorphism](#isomorphisms) or a
[base isomorphism](#fiber-products) relates two such objects.

Every polynomial in the coordinates has a **normal form**: its remainder on
division by the reduced Gröbner basis of the relations. The basis belongs
to the degree-lexicographic order in which the first coordinate of the
declaration is the greatest. Two polynomials are equal in the coordinate
ring exactly when their normal forms are equal. For `X` below, the normal
form of `x^2` is `t`.

`Affine(K, n)[g₁, …, gₙ]` is another spelling of `spec[g₁, …, gₙ] over K`.
[Smooth affine objects](language/smooth-declarations.md#smooth-affine-objects)
gives its syntax and the rule on its dimension. The rules of this section
apply to it.

Rules:

- The path after the name of the object must name an implementation with the
  `presented_affine` representation. Any other declaration there is an error
  (`E_TYPE`), apart from a `smooth_affine` implementation, whose error
  [Smooth affine objects](language/smooth-declarations.md#smooth-affine-objects)
  gives. The same holds for a fiber product and for a principal open.
- The coordinates must be distinct. Otherwise it is an error
  (`E_AFFINE_COORDINATE`).
- An object must have at most 16 coordinates. Otherwise it is an error
  (`E_LIMIT`). [Limits](#limits) lists the other bounds.
- The names of a relation and of an image are the coordinates of the object.
  Any other name is an error (`E_AFFINE_COORDINATE`), including a coordinate
  of the base.
- The base must be a presented affine object. Any other declaration is an
  error (`E_AFFINE_BASE`).
- The implementation of the base must name the marker that the
  implementation of the object names. Otherwise it is an error (`E_TYPE`).
  The two implementations may differ.
- `by(…)` must give each coordinate of the base exactly one image. A missing,
  repeated or unknown coordinate of the base is an error (`E_AFFINE_BASE`).
  A declaration may omit `by` when the base has no coordinates.
- The structure map must send every relation of the base to zero in the
  coordinate ring of the object. Otherwise it is an error (`E_AFFINE_BASE`).
- A base chain must not return to one of its objects. A cyclic chain is an
  error (`E_AFFINE_BASE`), including an object that names itself as its base.
- A base chain must hold at most 16 objects. Otherwise it is an error
  (`E_LIMIT`).
- An object may name a base that the module declares after it. The order of
  the declarations does not change their meaning.
- The relations may generate the whole ring, as in `relations(1)`. The
  coordinate ring is then the zero ring, and the object is empty.

> **Implementation note.** The kernel expands each polynomial expression. It
> computes the reduced Gröbner basis of the relations and then verifies the
> basis by exact division, before it accepts the declaration. It stores the
> images of the structure map as normal forms. The frontend supplies no
> basis and no normal form. A stored basis that fails the verification is an
> error (`E_AFFINE_RELATION`); no source program reaches that error.

Example, from `profile.vast` and
[`main.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/packages/affine-geometry/src/main.vast):

```vast
{{#include ../examples/packages/affine-geometry/src/profile.vast:point}}
{{#include ../examples/packages/affine-geometry/src/main.vast:objects}}
```

`D` is the dual numbers $\operatorname{Spec}\, \mathbb{Q}[e]/(e^2)$. `X` is the
curve $x^2 = t$ over the line `S`, and its structure map sends $(t, x)$ to
$t$. `Origin` is the point $t = 0$ of `S`, and `DS` is the dual numbers over
that point. The base chain of `X` is `X`, `S`, `SpecQQ`.

The following declaration names a base with the coordinate `t` and gives it
no image:

```vast
{{#include ../examples/reject/packages/affine-missing-image/main.vast:declaration}}
```

```text
{{#include ../examples/reject/packages/affine-missing-image.stderr}}
```

## Morphisms over a base

A **morphism over a base** is a morphism $f \colon X \to Y$ of presented
affine objects together with an object $S$ on both base chains. It commutes
with the structure maps of $X$ and $Y$ to $S$.
`indexed morphism f: R<X, Y, S> = definition;` declares one at a relative
family `R`. The form is the `MorphismDeclaration` of
[Smooth maps](language/smooth-declarations.md#smooth-maps); this section has
the rules of a morphism at a relative family.

`pullback(y₁ -> p₁, …, yₖ -> pₖ)` gives the morphism in the pullback
direction. For each coordinate $y_i$ of the target it gives the image $p_i$,
a polynomial expression in the coordinates of the source. The morphism is the
one whose ring map sends each $y_i$ to $p_i$. On points it sends $x$ to
$(p_1(x), \dots, p_k(x))$. The other definitions name a morphism that the
objects determine:

| Definition | Morphism |
| --- | --- |
| `identity` | The identity of `X` |
| `structure` | The composite of the structure maps along the base chain of `X`, from `X` to `Y` |
| `first`, `second` | A projection of a [fiber product](#fiber-products) |
| `restrict(φ)` | The restriction of `φ` to [principal opens](#principal-opens) |

The declaration defines a function of no operands: `f()` is the morphism, of
type `R<X, Y, S>`. For an object `T`, a `T`-valued point of `X` over `S` is a
value of `R<T, X, S>`. Two morphisms from `X` to `Y` are equal exactly when
the normal forms of their images are equal.

Rules:

- A morphism at a family without the `smooth` representation must name
  exactly three objects: its source, its target and its base. Otherwise it is
  an error (`E_AFFINE_BASE`). The family must then be a relative family.
  Otherwise it is an error (`E_TYPE`).
- The source and the target must be presented affine objects. Otherwise it is
  an error (`E_AFFINE_BASE`).
- The base must lie on the base chain of the source and on the base chain of
  the target. Otherwise it is an error (`E_AFFINE_BASE`).
- `pullback(…)` must give each coordinate of the target exactly one image. A
  missing, repeated or unknown coordinate is an error
  (`E_AFFINE_COORDINATE`).
- Each image must be a polynomial expression in the coordinates of the
  source. Any other name in an image, including a coordinate of the target,
  is an error (`E_AFFINE_COORDINATE`).
- A declaration may list the images in any order.
- The images must send every relation of the target to zero in the
  coordinate ring of the source. Otherwise it is an error
  (`E_AFFINE_RELATION`).
- The morphism must commute with the structure maps: for each coordinate of
  the base, its image along $X \to S$ must equal its image along
  $X \to Y \to S$. Otherwise it is an error (`E_AFFINE_BASE`).
- `identity` must have one object as its source and its target. Otherwise it
  is an error (`E_AFFINE_BASE`).
- `structure` must have its target on the base chain of its source. Otherwise
  it is an error (`E_AFFINE_BASE`). With the source as its target it is the
  identity.
- A call of the declared function with operands is an error (`E_ARITY`).
- The [limits](#limits) apply to the checks of this section.

> **Implementation note.** The kernel stores each image as a normal form in
> the coordinate ring of the source, so that a comparison of morphisms
> compares stored polynomials. In a generated program a morphism is a value
> of `AlgebraRuntime.Map`, and the program imports that runtime only when it
> uses one.

Example:

```vast
{{#include ../examples/packages/affine-geometry/src/main.vast:morphisms}}
```

`p` and `q` are two `D`-valued points of `Line`, and `closed` is the point of
`D`. `toX` commutes with the structure maps, because both ways send `t` to
`0` in the coordinate ring of `DS`.

No morphism from the line to the dual numbers sends `e` to `t`:

```vast
{{#include ../examples/reject/packages/affine-relation/main.vast:declaration}}
```

```text
{{#include ../examples/reject/packages/affine-relation.stderr}}
```

## Morphism primitives

> **Syntax**
>
> ```text
> RelativeBinding -> `relative_compose` `(` Path `)`
>     | `relative_equal` `(` Path `)`
>     | `relative_view` `(` Path `,` Path `,` Path `)`
>     | `relative_coefficient` `(` Path `,` Path `,` Path `,`
>       CoordinateName `,` Polynomial `)`
>     | `relative_int_point` `(` Path `,` Path `,` Path `)`
>     | `relative_pair` `(` Path `,` Path `)`
> ```

`indexed primitive p = binding;` declares a function `p` whose operands and
result the binding fixes. In the table, `R` is a relative family, and the
other letters are presented affine objects.

| Binding | Operands | Result | Value |
| --- | --- | --- | --- |
| `relative_compose(R)` | `R<Y, Z, S>`, `R<X, Y, S>` | `R<X, Z, S>` | The first morphism after the second |
| `relative_equal(R)` | `R<X, Y, S>`, `R<X, Y, S>` | `Bool` | Whether the two morphisms are equal |
| `relative_view(R, S, T)` | `R<X, Y, S>` | `R<X, Y, T>` | The same morphism, as a morphism over `T` |
| `relative_coefficient(R, X, Y, c, m)` | `R<X, Y, S>` | `Pair<Int>` | The coefficient of the monomial `m` in the normal form of the image of the coordinate `c`, as a reduced numerator and a positive denominator |
| `relative_int_point(R, X, P)` | One operand of type `Int` for each coordinate of `X` | `R<P, X, P>` | The point of `X` with these coordinates, in coordinate order |
| `relative_pair(R, F)` | `R<T, L, B>`, `R<T, M, B>` | `R<T, F, B>` | The morphism into the [fiber product](#fiber-products) `F` of `L` and `M` |

`relative_compose` composes in the written order: its first operand is
applied after its second. The images of the composite are the images of the
first operand, with the images of the second operand substituted for the
coordinates. `relative_coefficient` reads a coefficient that is zero as
`(0, 1)`. Its monomial `1` selects the constant term.

Rules:

- The family `R` must be a relative family. Otherwise it is an error
  (`E_TYPE`).
- In `relative_view(R, S, T)`, `T` must lie on the base chain of `S`.
  Otherwise it is an error (`E_TYPE`).
- In `relative_coefficient(R, X, Y, c, m)`, `X` and `Y` must be presented
  affine objects. Otherwise it is an error (`E_AFFINE_BASE`).
- The coordinate `c` must be a coordinate of `Y`. Otherwise it is an error
  (`E_AFFINE_COORDINATE`).
- The selector `m` must be a polynomial expression in the coordinates of `X`
  that expands to one monomial with the coefficient one. Any other
  polynomial is an error (`E_AFFINE_COORDINATE`), including `0` and an
  expression that cancels to zero.
- In `relative_int_point(R, X, P)`, the relations of `X` must generate the
  zero ideal, and `P` must be such an object without coordinates. Otherwise
  it is an error (`E_TYPE`).
- The result type `R<P, X, P>` of `relative_int_point(R, X, P)` must be an
  indexed type by the rules of
  [Indexed types of a family](indexed-source.md#indexed-types-of-a-family).
  In particular, `P` must lie on the base chain of `X`. Otherwise the
  declaration is an error (`E_TYPE`).
- In `relative_pair(R, F)`, `F` must be a fiber product that is declared
  without `via`. Otherwise it is an error (`E_TYPE`).
- The declaration does not check the result types of the calls of
  `relative_view` and `relative_pair`. A call whose result type is not an
  indexed type is an error (`E_ENDPOINT`), as
  [Calls of primitives](indexed-source.md#calls-of-primitives) says. Such a
  call has the result `R<X, Y, T>` or `R<T, F, B>`, and the parameter of `R`
  at the position of `T` or `F` does not admit it.
- The rules of [operand checks](#operand-checks) apply.

> **Implementation note.** A generated program substitutes and reduces at
> each call of a `relative_compose` primitive, without the [limits](#limits)
> of the compiler's own checks. `relative_view` returns its operand
> unchanged.

Example, from `profile.vast` and `main.vast`:

```vast
{{#include ../examples/packages/affine-geometry/src/profile.vast:primitives}}
{{#include ../examples/packages/affine-geometry/src/main.vast:observers}}
```

`same(p(), q())` is `false`, and `eps(p())` is `(1, 1)`. After the point
`closed` the two morphisms agree:
`same(compose(p(), closed()), compose(q(), closed()))` is `true`.
`compose(sq(), shift())` pulls `t` back to $(t + 1)^2$, and
`compose(shift(), sq())` pulls it back to $t^2 + 1$. `slope` reads `(2, 1)`
from the first and `(0, 1)` from the second. `compose(toS(), toX())` equals
`dsToS()`. `at(3)` is the point 3 of `Line`, and
`value(compose(sq(), at(3)))` is `(9, 1)`.

A **view** of a morphism is the same morphism over an object further along
the base chain of its base. A primitive with the binding `relative_view`
gives it. In
[`examples/packages/stdlib-affine/main.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/packages/stdlib-affine/main.vast),
`Curve` is the curve $x^2 = t$ over the library's `Line`. `curveToLine()` is
its structure map, a morphism over `Line`, and `overPoint(curveToLine())` is
the same morphism over `SpecQQ`:

```vast
{{#include ../examples/packages/stdlib-affine/main.vast:view}}
```

The compiler rejects a selector with two terms:

```vast
{{#include ../examples/reject/packages/affine-selector/main.vast:declaration}}
```

```text
{{#include ../examples/reject/packages/affine-selector.stderr}}
```

## Isomorphisms

> **Syntax**
>
> ```text
> IsomorphismDeclaration -> `indexed` `iso` IDENTIFIER
>     `=` `forward` Path `inverse` Path `;`
> ```

`indexed iso e = forward f inverse g;` declares an **isomorphism**: the
checked statement that the declared morphisms `f` and `g` are inverse to each
other. An isomorphism is a declaration. It is not a function, and no
primitive takes it as an operand.

Rules:

- Both paths must name declared morphisms over a base. Any other declaration
  is an error (`E_TYPE`).
- The two morphisms must belong to one relative family and have one base, and
  the source of each must be the target of the other. Otherwise it is an
  error (`E_AFFINE_BASE`).
- Both composites must be identities. Otherwise it is an error
  (`E_AFFINE_RELATION`).
- A call of an isomorphism is an error (`E_TYPE`).
- The [limits](#limits) apply to the two composites.

Example: the principal opens `U1` and `U2` of two lines, where $x$ and $y$
have inverses, are isomorphic by $y = 1/x$.

```vast
{{#include ../examples/packages/affine-geometry/src/main.vast:transition}}
```

Doubling is not its own inverse:

```vast
{{#include ../examples/reject/packages/affine-not-inverse/main.vast:declarations}}
```

```text
{{#include ../examples/reject/packages/affine-not-inverse.stderr}}
```

## Fiber products

> **Syntax**
>
> ```text
> FiberProduct -> `fiber` `(` Path `,` Path `)` BaseIsomorphism?
> BaseIsomorphism -> `via` `(` ImageBindings? `)`
>     `inverse` `(` ImageBindings? `)`
> ```

`indexed affine F(Impl) = fiber(L, M);` declares the
[fiber product](appendix/glossary.md#fiber-product) $L \times_B M$ of two
presented affine objects over the base $B$ of `L`. It is a presented affine
object with this presentation:

- Its coordinates are the coordinates of `L` and then those of `M`. Each is
  qualified by the name of its factor, as in `X::x`. When both factors have
  the same name, the qualifiers are `first` and `second`, as in `first::t`. A
  coordinate of a factor that is itself a fiber product keeps its
  qualifiers, as in `Fiber::X::x`.
- Its relations are the relations of both factors and, for each coordinate of
  `B`, the difference of its images under the two structure maps.
- Its base is `B`, and its structure map is that of `L`.

A morphism with the definition `first` is the projection $F \to L$, and one
with the definition `second` is the projection $F \to M$. A
`relative_pair(R, F)` primitive takes two morphisms $T \to L$ and $T \to M$
over `B` and gives the morphism $T \to F$ whose composites with the
projections are the two operands. Its
[syntax and operands](#morphism-primitives) are with the other primitives.

A **base isomorphism** `via(…) inverse(…)` declares a fiber product of
factors over two separately declared bases, $B$ for `L` and $B'$ for `M`.
`via` gives each coordinate of $B$ its image, a polynomial expression in the
coordinates of $B'$. `inverse` gives each coordinate of $B'$ its image in
the coordinates of $B$. The structure map of `M` to $B$ is then its
structure map to $B'$ followed by the base isomorphism.

Rules:

- Both factors must be presented affine objects. Otherwise it is an error
  (`E_AFFINE_BASE`).
- The first factor must have a base. Otherwise it is an error
  (`E_AFFINE_BASE`).
- Without a base isomorphism, the base of the second factor must be the base
  of the first, as one declaration. Otherwise it is an error
  (`E_AFFINE_BASE`), even when the two bases have the same presentation.
- With a base isomorphism, the second factor must have a base. Otherwise it
  is an error (`E_AFFINE_BASE`).
- `via(…)` must give each coordinate of $B$ exactly one image, and
  `inverse(…)` each coordinate of $B'$. A missing, repeated or unknown
  coordinate is an error (`E_AFFINE_BASE`).
- Each image of `via(…)` must be a polynomial expression in the coordinates
  of $B'$, and each image of `inverse(…)` one in the coordinates of $B$. Any
  other name is an error (`E_AFFINE_COORDINATE`).
- The two maps of a base isomorphism must send the relations of each base to
  zero in the coordinate ring of the other, and both composites must be
  identities. Otherwise it is an error (`E_AFFINE_RELATION`).
- A name of the fiber product's own coordinates must carry its qualifiers.
  An unqualified name is an error (`E_AFFINE_COORDINATE`).
- The source of a `first` or `second` morphism must be a fiber product, and
  its target must be the first or the second factor. Otherwise it is an error
  (`E_AFFINE_BASE`).
- The two operands of a `relative_pair(R, F)` primitive must have one source
  and the base of `F` as their base. Their targets must be the first and the
  second factor of `F`, in this order. Otherwise it is an error
  (`E_ENDPOINT`), as [operand checks](#operand-checks) says.
- The rules of [presented affine objects](#presented-affine-objects) and the
  [limits](#limits) apply to the derived presentation. In particular, the two
  factors together must have at most 16 coordinates (`E_LIMIT`).

> **Implementation note.** The kernel derives the presentation from the
> stored data of the factors and computes its basis. Each later audit derives
> the presentation again and compares it.

Example: the fiber of the curve `X` over the point `Origin` of `S`.

```vast
{{#include ../examples/packages/affine-geometry/src/main.vast:fiber}}
{{#include ../examples/packages/affine-geometry/src/main.vast:pair}}
```

`lift(toX(), toOrigin())` is the morphism from `DS` to `Fiber`, and
`compose(prX(), lift(toX(), toOrigin()))` equals `toX()`.

`S2` below is a second declaration of the line `S`. The fiber product over
the two bases names the base isomorphism:

```vast
{{#include ../examples/packages/affine-geometry/src/main.vast:via}}
```

Without the base isomorphism, the compiler rejects such a fiber product:

```vast
{{#include ../examples/reject/packages/affine-separate-bases/main.vast:declarations}}
```

```text
{{#include ../examples/reject/packages/affine-separate-bases.stderr}}
```

## Cartesian squares

> **Syntax**
>
> ```text
> CartesianDeclaration -> `indexed` `cartesian` IDENTIFIER `=` `square`
>     `(` Path `,` Path `)` `through` Path `inverse` Path `;`
> ```

`indexed cartesian c = square(a, b) through F inverse h;` declares a
**Cartesian square**. It is the checked statement that the common source $T$
of the declared morphisms `a` and `b` is the fiber product `F`. The morphisms
$a \colon T \to L$ and $b \colon T \to M$ give the morphism
$(a, b) \colon T \to F$, and `h` is its inverse $F \to T$. A Cartesian square
is a declaration. It is not a function, and no primitive takes it as an
operand.

Rules:

- `a`, `b` and `h` must name declared morphisms over a base. Any other
  declaration is an error (`E_TYPE`).
- The three morphisms must belong to one relative family. Otherwise it is an
  error (`E_AFFINE_BASE`).
- `F` must be a fiber product that is declared without a base isomorphism.
  Otherwise it is an error (`E_AFFINE_BASE`).
- `a` and `b` must have one source. Their targets must be the first and the
  second factor of `F`, in this order. `h` must lead from `F` to that source.
  The base of all three must be the base of `F`. Otherwise it is an error
  (`E_AFFINE_BASE`).
- Both composites of $(a, b)$ and `h` must be identities. Otherwise it is an
  error (`E_AFFINE_RELATION`).
- A call of a Cartesian square is an error (`E_TYPE`).
- The [limits](#limits) apply to the two composites.

Example: the fiber of the curve $x^2 = t$ over $t = 0$ is the dual numbers.

```vast
{{#include ../examples/packages/affine-geometry/src/main.vast:cartesian}}
```

The following morphism from the fiber forgets `x`, so it is no inverse:

```vast
{{#include ../examples/reject/packages/affine-square/main.vast:declarations}}
```

```text
{{#include ../examples/reject/packages/affine-square.stderr}}
```

## Principal opens

> **Syntax**
>
> ```text
> PrincipalOpen -> `localize` `(` Path `,` Polynomial `)` `inverse` IDENTIFIER
> ```

`indexed affine U(Impl) = localize(X, f) inverse u;` declares the **principal
open** $D(f)$ of the presented affine object `X`: the open subset on which
the polynomial $f$ has an inverse. With $A$ the coordinate ring of `X`, it is
$\operatorname{Spec}\, A[u]/(u f - 1)$, a presented affine object with this
presentation:

- Its coordinates are the coordinates of `X` and then `u`.
- Its relations are the relations of `X` and $u f - 1$.
- Its base is `X`, and its structure map is the inclusion $D(f) \to X$, which
  sends each coordinate of `X` to itself.

A morphism from `U` to `X` with the definition `structure` is therefore the
inclusion.

`restrict(φ)` defines the restriction of a declared morphism
$\varphi \colon Y \to X$ to principal opens: the morphism
$D(\varphi^{\#}(f)) \to D(f)$, where $\varphi^{\#}(f)$ is the image of $f$
in the coordinate ring of `Y`. It gives each coordinate of `X` its image
under $\varphi$, and it sends the inverse of $f$ to the inverse of
$\varphi^{\#}(f)$. This is the action of $\varphi$ on the structure sheaf
over a principal open.

Rules:

- `X` must be a presented affine object. Otherwise it is an error
  (`E_AFFINE_BASE`).
- `f` must be a polynomial expression in the coordinates of `X`. Any other
  name is an error (`E_AFFINE_COORDINATE`).
- `u` must differ from every coordinate of `X`. Otherwise it is an error
  (`E_AFFINE_COORDINATE`).
- `f` may be zero in the coordinate ring of `X`. The principal open is then
  empty.
- The path of `restrict(…)` must name a declared morphism over a base. Any
  other declaration is an error (`E_TYPE`).
- The source and the target of a `restrict(φ)` morphism must be principal
  opens. Otherwise it is an error (`E_AFFINE_BASE`).
- `φ` must lead from the object of the source open to the object of the
  target open. Otherwise it is an error (`E_AFFINE_BASE`).
- The source open must be the preimage of the target open: the polynomial of
  the source open and $\varphi^{\#}(f)$ must have one normal form. Otherwise
  it is an error (`E_AFFINE_BASE`).
- `φ` may itself be a `restrict(…)` morphism. Restrictions that name each
  other in a cycle are an error (`E_TYPE`).
- The rules of [presented affine objects](#presented-affine-objects), of
  [morphisms over a base](#morphisms-over-a-base) and the [limits](#limits)
  apply. In particular, `X` must have at most 15 coordinates (`E_LIMIT`).

> **Implementation note.** The kernel derives the presentation of a
> principal open from the stored data of its object, as it does for a fiber
> product. It elaborates restrictions after the morphisms that they name.

Example:

```vast
{{#include ../examples/packages/affine-geometry/src/main.vast:opens}}
{{#include ../examples/packages/affine-geometry/src/main.vast:zero}}
```

`Dt` is the line without its origin. `sq` pulls `t` back to `t^2`, so the
preimage of `Dt` is `Dt2`, and `onOpens` sends `u` to `v`. `Nothing` is the
empty open $D(0)$.

`Punctured` below inverts `t`, and the preimage of that open under `sq`
inverts `t^2`:

```vast
{{#include ../examples/reject/packages/affine-not-preimage/main.vast:declarations}}
```

```text
{{#include ../examples/reject/packages/affine-not-preimage.stderr}}
```

## Limits

The compiler checks the declarations of this chapter by exact polynomial
arithmetic. [Appendix D](appendix/limits.md#exact-affine-algebra)
lists the bounds of that arithmetic with their values.

Rules:

- [Presented affine objects](#presented-affine-objects) gives the limits on
  the coordinates of an object (`algebraGenerators`) and on the objects of a
  base chain (`algebraChain`). An object must also have at most
  `algebraRelations` relations.
- Every polynomial that a check produces must have at most `algebraTerms`
  terms, and each check must stay within `algebraWork` units of work. This
  covers the basis of an object and the images of a morphism. It covers the
  structure maps that a check composes along a base chain, a base
  isomorphism, and the composites of an isomorphism or of a Cartesian
  square.
- A declaration beyond one of these bounds, or beyond another bound of that
  table, is an error (`E_LIMIT`), even when its text is short. One example is
  a morphism that sends a coordinate with the relation `t^16` to a sum of 16
  coordinates: its check produces too many terms. Another is the cyclic
  system of five relations in five coordinates: its basis takes too much
  work.
- The bounds of [polynomial expressions](language/smooth-declarations.md#polynomial-expressions)
  on literals, levels, exponents and degrees apply to each expression.

## Operand checks

These rules apply to every call of a primitive of this chapter.

Rules:

- A call must have the number of operands that the binding fixes. Otherwise it
  is an error (`E_ARITY`).
- An operand of a `relative_int_point` primitive must have type `Int`.
  Otherwise it is an error (`E_TYPE`).
- An operand whose kind does not fit the table of bindings is an error
  (`E_TYPE`). This covers a value that is not a value of a family, such as an
  `Int` or a `Bool`, in the place of a morphism. It also covers a value of a
  family with a number of object arguments other than three as an operand of
  `relative_compose`, `relative_view` or `relative_pair`.
- Any other operand from the wrong family, or with the wrong source, target
  or base, is an error (`E_ENDPOINT`). Examples are two morphisms whose
  middle objects differ, a morphism of another relative family, and a
  morphism into a second declaration of the expected object.
- The `E_ENDPOINT` message names the first failed check: the operand, the
  family, object or base that the binding expects, and the one supplied. The
  compiler checks families before objects, and the objects of
  `relative_compose` before its base.

In this program `Copy` has the presentation of `Line`, and `r` is a morphism
into `Copy`:

```vast
{{#include ../examples/reject/packages/affine-other-object/main.vast:program}}
```

```text
{{#include ../examples/reject/packages/affine-other-object.stderr}}
```

## Scope of presented affine geometry

Presented affine geometry covers the declarations of this chapter. Its only
field of coefficients is the rational numbers. A function body composes,
views and pairs declared morphisms, and it builds rational points from
integers. It creates no object and no other morphism. An
[isomorphism](#isomorphisms) between principal opens states a transition
between two objects. The language has no declaration that glues objects along
such transitions, as the projective line needs, and it checks no covers and
no cocycle conditions. Smooth
affine geometry is in
[Smooth affine declarations](language/smooth-declarations.md), and the
descriptor objects of the core are in
[Geometric types](language/geometric-types.md).
