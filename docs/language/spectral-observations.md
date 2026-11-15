# Spectral observations

This chapter defines the free modules and the endomorphism fields of smooth
affine objects, their spectral pairs and invariants, the finite charts on
which their eigenvalues are simple, and the primitive bindings that observe
them. Let `X` be a smooth affine object with the coordinates x₁, …, xₘ, and
let A be the ring of the polynomials in x₁, …, xₘ with rational
coefficients. A **free module** on `X` is Aⁿ with a named ordered basis of n
vectors. An **endomorphism field** of a free module V is an n × n matrix H
whose entries are elements of A. At a point p of `X` its value H(p) is a
matrix of rational numbers. [Smooth affine declarations](smooth-declarations.md)
defines smooth affine objects, smooth maps, cotangent fibers and the
[failure value](smooth-declarations.md#fiber-primitives) ⊥. The general rules
of `indexed` declarations are in [Indexed declarations](../indexed-source.md).
[Notation](notation.md) explains the Syntax blocks, and the
[glossary](../appendix/glossary.md) defines the terms.

A path in a declaration or a binding of this chapter that resolves to
nothing is an error of [resolution](names-and-paths.md#resolution)
(`E_NAME`), before the rules of this chapter apply. A rule below that
requires a path to name a declaration of some kind, such as a spectrum
declaration, concerns a path that names a declaration of another kind.

The examples quote the tested package
[`examples/packages/spectral-observations/`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/spectral-observations),
whose executable prints `42`. Each rejected program is a package on the
profile of the standard library. It appears with the diagnostic that the
compiler prints for it.

The declarations of this chapter are the forms of `SpectralDeclaration`:

> **Syntax**
>
> ```text
> SpectralDeclaration -> SpectralFamily | FreeModuleDeclaration
>     | EndomorphismDeclaration | SpectrumDeclaration | BranchDeclaration
> ```

Each declaration of this chapter is an [item](items.md):
`SpectralDeclaration` is one form of
[`IndexedDeclaration`](../indexed-source.md). So is `PrimitiveDeclaration`,
whose bindings in this chapter are the forms of `SpectralBinding`. A
`MorphismDeclaration` of [Smooth maps](smooth-declarations.md#smooth-maps)
may have a definition of this chapter, a form of `SpectralInvariant`. `pub`
before a declaration makes it visible outside its module.

## The spectral profile

> **Syntax**
>
> ```text
> SpectralFamily -> `indexed` `family` IDENTIFIER `(` Parameters? `)`
>     `=` SpectralRepresentation `constraints` `(` Constraints? `)` `;`
> SpectralRepresentation -> `free_module` | `endomorphism` | `spectrum` | `branch`
> ```

[Families](../indexed-source.md#families) gives the productions
`Parameters` and `Constraints`.

A family of this chapter has the types that its declarations name. None of
the types has a value. In the table, `X` is a smooth affine object.

| Representation | Indexed type | The declarations that name it |
| --- | --- | --- |
| `free_module` | `FreeModule<X>` | The [free modules](#free-modules) on `X` |
| `endomorphism` | `Endomorphism<X>` | The [endomorphism fields](#endomorphism-fields) on `X` |
| `spectrum` | `Spectrum<X>` | The [spectral pairs](#spectral-pairs) of the fields on `X` |
| `branch` | `Branch<X>` | The [finite charts](#branches) of the spectra on `X` |

Rules:

- A family with one of these representations must have exactly one
  parameter, of the form `object(K)`, and exactly the constraint
  `canonical(0)`. Otherwise it is an error (`E_TYPE`).
- Every implementation in the domain of `K` must have the `smooth_affine`
  representation. Otherwise it is an error (`E_TYPE`).

`std::linalg::spectral` declares the families `FreeModule`, `Endomorphism`,
`Spectrum` and `Branch` over the classification `CInfAffine` of
`std::geometry::smooth::affine`. It declares no free module, field,
spectrum, branch, invariant or observation. A program declares them, as it
declares its metrics and its frames. The module, from
[`mod.vast`](https://github.com/MGYamada/Vastitas/blob/main/stdlib/src/linalg/spectral/mod.vast):

```vast
{{#include ../../stdlib/src/linalg/spectral/mod.vast}}
```

## Free modules

> **Syntax**
>
> ```text
> FreeModuleDeclaration -> `indexed` `free_module` IDENTIFIER `:` Path
>     `<` Path ( `,` Path )* `>` `=` `basis` `(` BasisNames? `)` `;`
> BasisNames -> IDENTIFIER ( `,` IDENTIFIER )* `,`?
> ```

`indexed free_module V: F<X> = basis(e₁, …, eₙ);` declares the free module
V = Aⁿ on the object `X` at the family `F`, with the ordered basis
e₁, …, eₙ. The rank of V is n. A basis name names a row and a column of the
matrices that act on V. It is not a value, a coordinate or a declaration, so
it may be spelled like a coordinate.

A free module is a declaration. It is not a value, and two free modules are
different modules, even when their bases have the same names.

Rules:

- The family must have the `free_module` representation. Otherwise it is an
  error (`E_SPECTRAL`).
- A free module must name exactly one object. Otherwise it is an error
  (`E_SPECTRAL`).
- The object must be a smooth affine object, and the family must accept it.
  Otherwise it is an error (`E_SPECTRAL`).
- The basis must have at most `spectralRank` = 4 names
  ([limits](../appendix/limits.md#spectral-observations)). Otherwise it is
  an error (`E_LIMIT`). The kernel checks the rank first, so a basis of five
  names is an error (`E_LIMIT`) even when a name repeats.
- The basis must have at least one name. Otherwise it is an error
  (`E_SPECTRAL`).
- The names of the basis must be different. A name that occurs twice is an
  error (`E_SPECTRAL`).
- A free module used as a value is an error (`E_TYPE`).

Example, from
[`profile.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/packages/spectral-observations/src/profile.vast):

```vast
{{#include ../../examples/packages/spectral-observations/src/profile.vast:field}}
```

`V` is A² with the basis `e1`, `e2`, where A is the ring of polynomials in x
and y.

The following free module has five basis vectors:

```vast
{{#include ../../examples/reject/packages/spectral-rank-limit/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/spectral-rank-limit.stderr}}
```

## Endomorphism fields

> **Syntax**
>
> ```text
> EndomorphismDeclaration -> `indexed` `endomorphism` IDENTIFIER `:` Path
>     `<` Path ( `,` Path )* `>` `=` `rows` `(` EndomorphismRows? `)`
>     `of` Path `symmetric`? `;`
> EndomorphismRows -> EndomorphismRow ( `,` EndomorphismRow )* `,`?
> EndomorphismRow -> `(` ( Polynomial ( `,` Polynomial )* `,`? )? `)`
> ```

[Polynomial expressions](smooth-declarations.md#polynomial-expressions)
gives the production `Polynomial`.

`indexed endomorphism H: F<X> = rows(r₁, …, rₙ) of V;` declares the
endomorphism field H of the free module V at the family `F`. Each
parenthesized group rᵢ is row i of H: entry j of rᵢ is the entry Hᵢⱼ, a
polynomial expression in the coordinates of `X`. Row i and column j belong
to the basis vectors eᵢ and eⱼ of V. H acts on V by the matrix product: the
components of Hv in the basis are H times the components of v, so column j
of H holds the components of H eⱼ.

`symmetric` after the module claims that H = Hᵀ, and the kernel checks the
claim. Without `symmetric` the declaration makes no claim, even when H is
symmetric. The claim selects the pairing Re tr(KX) of symmetric matrices,
which the [Daleckii–Krein statements](../daleckii-krein.md) of the
mathematical bridge use. The profile inserts no conjugation, metric or
adjoint.

An endomorphism field is a declaration. It is not a value.

Rules:

- The family must have the `endomorphism` representation. Otherwise it is
  an error (`E_SPECTRAL`).
- An endomorphism field must name exactly one object. Otherwise it is an
  error (`E_SPECTRAL`).
- The object must be a smooth affine object, and the family must accept it.
  Otherwise it is an error (`E_SPECTRAL`).
- The path after `of` must name a free module declaration. Otherwise it is
  an error (`E_SPECTRAL`).
- The free module must be a module on the object of the field. Otherwise it
  is an error (`E_SPECTRAL`), even when the two objects have one dimension.
- For a free module of rank n, `rows(…)` must have n rows, each of n
  entries. Otherwise it is an error (`E_SPECTRAL`).
- The rules of [polynomial expressions](smooth-declarations.md#polynomial-expressions)
  apply to each entry, with the coordinates of the object. Any other name in
  an entry, including the fiber coordinate of a spectrum, is an error
  (`E_AFFINE_COORDINATE`). All entries of one field share one work budget.
- A field declared `symmetric` must have Hᵢⱼ = Hⱼᵢ as polynomials, for all i
  and j. Otherwise it is an error (`E_SPECTRAL`), whose message names the
  first entry, by the names of the basis, that differs from its mirror.
- A missing `of` and a row that is not a parenthesized group are errors
  (`E_PARSE`).
- An endomorphism field used as a value is an error (`E_TYPE`).

The example declares the field H = rows((x, y), (y, −x)) of `V` in the
section above. At the point (3, 4), H(p) has the rows (3, 4) and (4, −3).
The program also declares four constant fields on the point `Pt`, whose
coordinate ring is the rational numbers:

```vast
{{#include ../../examples/packages/spectral-observations/src/profile.vast:point}}
```

The following field is declared `symmetric`, and its entry (e1, e2) is y
while its entry (e2, e1) is −y:

```vast
{{#include ../../examples/reject/packages/spectral-not-symmetric/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/spectral-not-symmetric.stderr}}
```

The following field is a field of a second plane, and `V` is a module of the
first:

```vast
{{#include ../../examples/reject/packages/spectral-other-object/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/spectral-other-object.stderr}}
```

## Spectral pairs

> **Syntax**
>
> ```text
> SpectrumDeclaration -> `indexed` `spectrum` IDENTIFIER `:` Path
>     `<` Path ( `,` Path )* `>` `=` `eigen` `(` Path `,` IDENTIFIER `)` `;`
> ```

`indexed spectrum S: F<X> = eigen(H, t);` declares the spectral pair of the
field H at the family `F`, with the fiber coordinate `t`. The **fiber
coordinate** of a spectrum is a variable that follows the coordinates of
`X`: the polynomials of the spectrum are elements of A[t], the polynomials
in x₁, …, xₘ and t. The characteristic polynomial of H is

$$
\chi_H(x, t) = \det(tI - H(x)) = \sum_{i=0}^{n} \chi_i(x)\, t^i ,
$$

monic of degree n in t, and χ′ is its partial derivative in t. The
**spectral pair** of H is the characteristic scheme Σ_H, the spectrum of the
ring A[t]/(χ_H), together with the module of H: V, on which t acts as H.
The kernel computes χ_H and the adjugate adj(tI − H), the matrix with
(tI − H)·adj(tI − H) = adj(tI − H)·(tI − H) = χ_H·I, and checks both before
it accepts the declaration. No source text and no request holds them.

Σ_H is always the characteristic scheme. It is never replaced by the reduced
spectrum, by the distinct eigenvalues or by the locus of the annihilator of
the module: a scalar field and a Jordan block with the same characteristic
polynomial have different spectral pairs, which the
[module observations](#module-observations) tell apart.

A spectrum is a declaration. It is not a value, and it computes, orders and
chooses no eigenvalue.

Rules:

- The family must have the `spectrum` representation. Otherwise it is an
  error (`E_SPECTRAL`).
- A spectrum must name exactly one object. Otherwise it is an error
  (`E_SPECTRAL`).
- The object must be a smooth affine object, and the family must accept it.
  Otherwise it is an error (`E_SPECTRAL`).
- The first argument of `eigen` must name an endomorphism declaration.
  Otherwise it is an error (`E_SPECTRAL`).
- The field must be a field on the object of the spectrum. Otherwise it is
  an error (`E_SPECTRAL`).
- The fiber coordinate must be neither a coordinate of the object nor a
  name of the basis of the free module of the field. Otherwise it is an
  error (`E_SPECTRAL`). It may be the name of another declaration.
- The fiber coordinate is an identifier, not a path. A path there is an
  error (`E_PARSE`).
- The computation and the checks of the spectral pair must stay within the
  term and work budgets of
  [exact affine algebra](../appendix/limits.md#exact-affine-algebra).
  Otherwise it is an error (`E_LIMIT`).
- A spectrum used as a value is an error (`E_TYPE`).

The example of the section above declares the spectra of the four constant
fields. The fields `Zero` and `N` have χ = t², and `TwoI` and `J` have
χ = (t − 2)². For the field H on the plane, χ = t² − x² − y² and
adj(tI − H) = tI + H, so χ′ = 2t.

> **Implementation note.** The kernel computes χ_H and adj(tI − H) with the
> Faddeev–LeVerrier recursion (`SpectralDeclarations.faddeevLeVerrier` in
> the kernel). It then checks, within one work budget: χ_H equals the
> cofactor expansion of det(tI − H), a second route; (tI − H)·adj = χ_H·I
> and adj·(tI − H) = χ_H·I; the trace of the adjugate is χ′; χ_H(H) = 0 in
> the n × n matrices over A (Cayley–Hamilton); adj² − χ′·adj is a multiple
> of χ_H; and ∂ᵢχ_H + tr(adj·∂ᵢH) = 0 for each coordinate xᵢ (Jacobi's
> formula). Each identity modulo χ_H is checked against a quotient that the
> kernel computes and multiplies back, so no check depends on the division.
> A failed check is an error (`E_SPECTRAL`) that names the identity. The
> declaration audit checks every spectrum again
> (`SpectralDeclarations.checkSpectrum`), and it requires the fiber
> coordinate of a request to be an identifier, which no strict keyword is.
> The oracle theorem
> `VastitasOracle.SpectralDeclarations.checkCertificate_sound` states that
> an accepted spectrum satisfies the seven identities in every commutative
> ring that receives the rationals, and the bridge theorem
> `VastitasBridge.Spectral.toMv_charPoly` that χ_H is the characteristic
> polynomial of the field in Mathlib.

## Spectral invariants

> **Syntax**
>
> ```text
> SpectralInvariant -> `trace_power` `(` Path `,` INTEGER_LITERAL `)`
>     | `char_coefficient` `(` Path `,` INTEGER_LITERAL `)`
> ```

A **spectral invariant** is a smooth map that a morphism declaration defines
with `trace_power` or `char_coefficient`.
[Smooth maps](smooth-declarations.md#smooth-maps) gives the production
`MorphismDeclaration`. In the table, `S` is a family with the `smooth`
representation, `X` the object of the field or the spectrum, and `L` a
smooth affine object of dimension 1.

| Declaration | Map | Value at x |
| --- | --- | --- |
| `indexed morphism φ: S<X, L> = trace_power(H, k);` | X → L | tr(H(x)ᵏ) |
| `indexed morphism φ: S<X, L> = char_coefficient(Σ, i);` | X → L | χᵢ(x), the coefficient of tⁱ in the characteristic polynomial of the spectrum Σ |

A spectral invariant is an ordinary smooth map: `φ()` is the map, of type
`S<X, L>`, and every primitive of
[Smooth affine declarations](smooth-declarations.md) applies to it. Its
differential, its gradient under a metric and its compiled reverse pass are
those of the smooth map with the same polynomial, and it has no reverse rule
of its own. The kernel computes the polynomial from the declaration.

Rules:

- The family must have the `smooth` representation. Otherwise it is an error
  (`E_SPECTRAL`).
- An invariant must name exactly two objects, its source and its target.
  Otherwise it is an error (`E_SPECTRAL`).
- The source must be a smooth affine object, and the target a smooth affine
  object of dimension 1. Otherwise it is an error (`E_SPECTRAL`).
- The path of `trace_power` must name an endomorphism declaration, and the
  path of `char_coefficient` a spectrum declaration. Otherwise it is an error
  (`E_SPECTRAL`).
- The field or the spectrum must be on the source of the map. Otherwise it
  is an error (`E_SPECTRAL`).
- The power k and the index i must be unsigned integer literals (`E_PARSE`)
  with at most 64 digits (`E_LIMIT`).
- The power k must be at least 1. The power 0 is an error (`E_SPECTRAL`).
- The power k must be at most `spectralPower` = 8
  ([limits](../appendix/limits.md#spectral-observations)). Otherwise it is
  an error (`E_LIMIT`).
- The polynomial tr(Hᵏ) and each product that computes it must stay within
  the term and work budgets of
  [exact affine algebra](../appendix/limits.md#exact-affine-algebra).
  Otherwise it is an error (`E_LIMIT`).
- The index i must be at most the rank n of the field of the spectrum.
  Otherwise it is an error (`E_SPECTRAL`). The index n gives the constant
  map 1.
- A call of the declared function with operands is an error (`E_ARITY`).

Example, from `profile.vast`:

```vast
{{#include ../../examples/packages/spectral-observations/src/profile.vast:invariants}}
```

`tr1` is the map 0, and `tr2` is the map 2x² + 2y², which equals `ref2`.
`c0` is the map −x² − y². By Newton's identity for a field of rank 2,
χ₀ = ((tr H)² − tr(H²))/2, so `c0` is −1/2 times `tr2`, because tr H = 0.

The invariants of the four constant fields on the point, from `profile.vast`:

```vast
{{#include ../../examples/packages/spectral-observations/src/profile.vast:point-invariants}}
```

`two_tr1` and `j_tr1` are the constant 4, `two_tr2` and `j_tr2` the
constant 8, `two_c0` and `j_c0` the constant 4, and `two_c1` and `j_c1` the
constant −4. The invariants of `Zero` and `N` are all 0.

> **Implementation note.** The kernel computes tr(Hᵏ) by products of
> polynomial matrices, each charged to the work budget before it is
> computed, and it bounds each product and the trace by the term limit. A
> spectral invariant is a declared smooth map whose binding
> records its provenance, the field or the spectrum that it reads, so the
> declaration audit computes the polynomial again from that declaration and
> compares it. Its derivative rule is the rule of a declared smooth map, and
> [Compiled reverse Core](../spec/reverse-core.md) applies to it unchanged.
> The oracle theorem `VastitasOracle.SpectralDeclarations.invariant_sound`
> states that an accepted invariant is tr(Hᵏ) or the coefficient of the
> declared field, and `VastitasOracle.SpectralAcceptance.s4_trace_square_gradient`
> that the differential of `tr2` is the covector (4p₀, 4p₁) at every
> rational point p, which `sharp` with the identity matrix as its Gram
> inverse maps to the vector (4p₀, 4p₁). The bridge theorem
> `VastitasBridge.Spectral.toMv_tracePower` states that the polynomial is the
> trace of the k-th power of the field in Mathlib, and
> `VastitasBridge.Spectral.checked_trace_power_dk` that for a field declared
> `symmetric` an accepted `differential` of the invariant is the
> Daleckii–Krein cotangent composed with the derivative of the field.

## Module observations

> **Syntax**
>
> ```text
> SpectralBinding -> ModuleObservationBinding | BranchObservationBinding
> ModuleObservationBinding -> `annihilates` `(` Path `,` `spectrum` `=` Path
>       `,` `element` `=` Polynomial `)`
>     | `action_entry` `(` Path `,` `spectrum` `=` Path
>       `,` `element` `=` Polynomial `,` IDENTIFIER `,` IDENTIFIER `)`
> ```

`indexed primitive p = binding;` declares a function `p` whose operands and
result the binding fixes, as [Primitives](../indexed-source.md#primitives)
says. `SpectralBinding` gives the bindings of this chapter. In the tables of
this chapter, `S` is a family with the `smooth` representation, and `Z` is a
0-dimensional smooth affine object, so that a value of `S<Z, X>` is a
[rational point](smooth-declarations.md#smooth-map-primitives) of `X`.

The element f of a module observation is a polynomial in the coordinates of
`X` and the fiber coordinate t of the spectrum Σ:
f = Σₖ fₖ(x) tᵏ. At a point p it acts on V as the matrix
f(H(p)) = Σₖ fₖ(p) H(p)ᵏ, the action of t as H.

| Binding | Operands | Result | Value |
| --- | --- | --- | --- |
| `annihilates(S, spectrum = Σ, element = f)` | `S<Z, X>` | `Bool` | Whether f(H(p)) = 0 at the point p |
| `action_entry(S, spectrum = Σ, element = f, eᵢ, eⱼ)` | `S<Z, X>` | `Pair<Int>` | The entry in row eᵢ and column eⱼ of f(H(p)), as a reduced numerator and a positive denominator |

χ_H(H(p)) = 0 at every point p (Cayley–Hamilton), so f(H(p)) depends on f
modulo χ_H only. The observations are the action of A[t]/(χ_H) on the
module of the spectral pair. Two fields with one characteristic polynomial
and the same invariants can differ in it. An entry that is zero reads
`(0, 1)`.

Rules:

- `S` must have the `smooth` representation. Otherwise it is an error
  (`E_TYPE`).
- The path after `spectrum =` must name a spectrum declaration. Otherwise it
  is an error (`E_SPECTRAL`). A missing `spectrum =` or `element =` is an
  error (`E_PARSE`).
- The rules of [polynomial expressions](smooth-declarations.md#polynomial-expressions)
  apply to the element, with the coordinates of the object of the spectrum
  and its fiber coordinate. Any other name, including the fiber coordinate
  of another spectrum, is an error (`E_AFFINE_COORDINATE`).
- The row eᵢ and the column eⱼ of `action_entry` must be names of the basis
  of the free module of the field of the spectrum. Otherwise it is an error
  (`E_SPECTRAL`). A row or a column that is not an identifier is an error
  (`E_PARSE`).
- The rules of [operand checks](#operand-checks) apply.

Example, from
[`main.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/packages/spectral-observations/src/main.vast):

```vast
{{#include ../../examples/packages/spectral-observations/src/main.vast:action}}
```

On the point, t − 2 annihilates `TwoI` and not `J`: J − 2I has the rows
(0, 1) and (0, 0). So `act_two(o)` reads `(0, 1)` and `act_j(o)` reads
`(1, 1)`, although the two fields have the same characteristic polynomial
and the same invariants. (t − 2)² annihilates `J`, and t² annihilates `N`. On
the plane, t annihilates H(0, 0) and not H(3, 4), and `ann_chi` is true at
every point.

## Branches

> **Syntax**
>
> ```text
> BranchDeclaration -> `indexed` `branch` IDENTIFIER `:` Path
>     `<` Path ( `,` Path )* `>` `=` `simple` `(` Path
>     `,` `localize` `=` Polynomial `,` `witness` `=` Polynomial
>     `,` `exponent` `=` INTEGER_LITERAL `)` `;`
> ```

A **branch** of a spectrum is a finite chart on which every eigenvalue of
the field is simple. `indexed branch B: F<X> = simple(Σ, localize = g,
witness = W, exponent = e);` declares the branch of the spectrum Σ on the
principal open D(g), the points p of `X` with g(p) ≠ 0. g is an element of
A, and the **gap witness** W is an element of A[t] of degree below n in t.
The kernel accepts the branch only when

$$
W \cdot \chi' - g^{e} \equiv 0 \pmod{\chi} ,
$$

that is, when W·χ′ − gᵉ is a multiple of χ in A[t]. At a point p with
g(p) ≠ 0 and a root t of χ(p, ·), the identity gives W(p, t)·χ′(p, t) =
g(p)ᵉ ≠ 0, so χ′(p, t) ≠ 0: the root is simple. The certificate is an exact
identity of polynomials. No tolerance, sample or bound enters it.

A **branch point** of B is a pair (p, t) of a rational point p of `X` and a
rational number t with g(p) ≠ 0 and χ(p, t) = 0. There χ′(p, t) ≠ 0, so by
the implicit function theorem of real analysis the eigenvalue t extends,
near p, to a differentiable function λ of the real point with λ(p) = t and
χ(x, λ(x)) = 0. The language does not construct λ. The branch names no
eigenvalue: each [branch observation](#branch-observations) takes the
eigenvalue as an operand.

A branch is a declaration. It is not a value, and it is not a smooth map.

Rules:

- The family must have the `branch` representation. Otherwise it is an
  error (`E_SPECTRAL`).
- A branch must name exactly one object. Otherwise it is an error
  (`E_SPECTRAL`).
- The object must be a smooth affine object, and the family must accept it.
  Otherwise it is an error (`E_SPECTRAL`).
- The first argument of `simple` must name a spectrum declaration. Otherwise
  it is an error (`E_SPECTRAL`).
- The spectrum must be a spectrum on the object of the branch. Otherwise it
  is an error (`E_SPECTRAL`).
- The fields must be `localize =`, `witness =` and `exponent =`, in this
  order. A missing or a misplaced field is an error (`E_PARSE`).
- The exponent e must be an unsigned integer literal (`E_PARSE`) with at
  most 64 digits (`E_LIMIT`), and at most `spectralPower` = 8
  ([limits](../appendix/limits.md#spectral-observations)). Otherwise it is
  an error (`E_LIMIT`). The kernel checks the exponent before the
  polynomials.
- The rules of [polynomial expressions](smooth-declarations.md#polynomial-expressions)
  apply to g and to W, with the coordinates of the object and the fiber
  coordinate of the spectrum. Any other name is an error
  (`E_AFFINE_COORDINATE`).
- The localization g must not contain the fiber coordinate. Otherwise it is
  an error (`E_SPECTRAL`).
- The localization g must not be zero. Otherwise it is an error
  (`E_SPECTRAL`).
- The gap witness W must have a degree in the fiber coordinate below the
  rank n of the field. Otherwise it is an error (`E_SPECTRAL`).
- W·χ′ − gᵉ must be a multiple of χ. Otherwise it is an error
  (`E_SPECTRAL`), whose message shows a term of the remainder of W·χ′ − gᵉ
  modulo χ, with the names of the coordinates and of the fiber coordinate,
  and the number of its terms. The computation must stay within the term
  and work budgets of
  [exact affine algebra](../appendix/limits.md#exact-affine-algebra).
  Otherwise it is an error (`E_LIMIT`).
- A branch used as a value is an error (`E_TYPE`).

Example, from `profile.vast`:

```vast
{{#include ../../examples/packages/spectral-observations/src/profile.vast:spectrum}}
```

For χ = t² − x² − y², χ′ = 2t, and (t/2)·2t = t², which is x² + y² modulo
χ. So the gap witness t/2 certifies D(x² + y²) with the exponent 1. The
chart leaves out the origin, where the two eigenvalues ±√(x² + y²) meet.

The localization 1 asks for the whole plane, the origin included:

```vast
{{#include ../../examples/reject/packages/spectral-gap-at-origin/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/spectral-gap-at-origin.stderr}}
```

No gap witness passes for g = 1 and this field. The eigenvalue 2 of the
Jordan block [[2, 1], [0, 2]] is double, so the block has no branch at all:

```vast
{{#include ../../examples/reject/packages/spectral-jordan-branch/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/spectral-jordan-branch.stderr}}
```

A gap witness that differs from a valid one by 10⁻²⁰·t fails too:

```vast
{{#include ../../examples/reject/packages/spectral-wrong-witness/main.vast:declarations}}
```

```text
{{#include ../../examples/reject/packages/spectral-wrong-witness.stderr}}
```

> **Implementation note.** The kernel computes the quotient Q of
> W·χ′ − gᵉ by χ, as a monic polynomial in t, and checks
> W·χ′ − gᵉ − Q·χ = 0 by multiplication and subtraction, so the check does
> not depend on the division. No request holds the quotient. The declaration
> audit checks every branch again (`SpectralDeclarations.checkBranch`). The
> oracle theorem `VastitasOracle.SpectralDeclarations.SpectralValid.unit_at`
> states that at a point of any commutative ring where χ vanishes and g has
> an inverse u, χ′ has the inverse W·uᵉ.
> `VastitasOracle.SpectralDeclarations.Examples.unit_gap_no_witness`
> states that the localization 1 has no gap witness, exponent and quotient
> at all for the characteristic polynomial of the example, and
> `Examples.origin_off_chart` that every localization that the gap check
> accepts for that polynomial vanishes at the origin.

## Branch observations

> **Syntax**
>
> ```text
> BranchObservationBinding -> `on_branch` `(` Path `,` Path `,` `branch` `=` Path `)`
>     | `branch_differential` `(` Path `,` Path `,` Path `,` `branch` `=` Path `)`
>     | `branch_projector` `(` Path `,` Path `,` `branch` `=` Path
>       `,` IDENTIFIER `,` IDENTIFIER `)`
> ```

In the table, `L` is a smooth affine object of dimension 1 and `C` a
[cotangent family](smooth-declarations.md#fiber-primitives). B is a branch
on `X` with the localization g, of the spectrum with the characteristic
polynomial χ of the field H. The operands are a point p, of type `S<Z, X>`,
and a value t, of type `S<Z, L>`, the rational number of a point of `L`. The
**eigenprojector** of a branch point (p, t) is the matrix

$$
P = \frac{\operatorname{adj}(tI - H(p))}{\chi'(p, t)} .
$$

| Binding | Operands | Result | Value |
| --- | --- | --- | --- |
| `on_branch(S, L, branch = B)` | `S<Z, X>`, `S<Z, L>` | `Bool` | Whether (p, t) is a branch point of B |
| `branch_differential(S, C, L, branch = B)` | `S<Z, X>`, `S<Z, L>` | `C<X>` | At a branch point, the covector −Σᵢ (∂ᵢχ(p, t)/χ′(p, t)) dxᵢ at p; ⊥ otherwise |
| `branch_projector(S, L, branch = B, eᵢ, eⱼ)` | `S<Z, X>`, `S<Z, L>` | `Pair<Int>` | At a branch point, the entry in row eᵢ and column eⱼ of P, as a reduced fraction; `(0, 0)` otherwise |

For the function λ of [Branches](#branches), the derivative of
χ(x, λ(x)) = 0 at p gives ∂ᵢχ + χ′·∂ᵢλ = 0, so the covector of
`branch_differential` is the differential dλ(p) of the eigenvalue. By
Jacobi's formula it is also Σᵢ tr(P·∂ᵢH(p)) dxᵢ (Hellmann–Feynman). The
eigenprojector satisfies P² = P, tr P = 1 and H(p)·P = P·H(p) = t·P. Each
column of P that is not zero is an eigenvector of H(p) for t, and P has such
a column. For a field declared `symmetric`, P is symmetric, because the
adjugate of a symmetric matrix is symmetric.

No observation computes, orders or chooses an eigenvalue. An eigenvalue that
is not rational has no branch point, because no rational t is a root. A
value that is not an eigenvalue, or a point off the chart, is no branch
point, even when χ(p, t) = 0.

Rules:

- `S` must have the `smooth` representation, and `C` the `cotangent`
  representation. Otherwise it is an error (`E_TYPE`).
- `L` must be a smooth affine object of dimension 1. Otherwise it is an
  error (`E_TYPE`).
- `branch_differential` takes its families in the order `S`, `C`, `L`. A
  line in the place of the cotangent family is an error (`E_TYPE`).
- The path after `branch =` must name a branch declaration. Otherwise it is
  an error (`E_SPECTRAL`). A missing `branch =` is an error (`E_PARSE`).
- The row eᵢ and the column eⱼ of `branch_projector` must be names of the
  basis of the free module of the field of the spectrum of the branch.
  Otherwise it is an error (`E_SPECTRAL`). A row or a column that is not an
  identifier is an error (`E_PARSE`).
- The rules of [operand checks](#operand-checks) apply.

Example, from `main.vast`:

```vast
{{#include ../../examples/packages/spectral-observations/src/main.vast:branch}}
```

At p = (3, 4), χ(p, t) = t² − 25, and the branch points over p are (p, 5)
and (p, −5). `on(p, line_at(5))` is `true`, and `on(p, line_at(4))` is
`false`. At the origin χ(0, 0, 0) = 0, and `on(z, line_at(0))` is `false`,
because the origin is off the chart. At (p, 5), ∂ₓχ = −2x, ∂ᵧχ = −2y and
χ′ = 2t, so `dlambda(p, line_at(5))` is the covector (3/5, 4/5), and at
(p, −5) it is (−3/5, −4/5). Under the Euclidean metric both are unit
covectors. The eigenprojector at (p, 5) is (1/5)[[4, 2], [2, 1]], so
`p12(p, line_at(5))` reads `(2, 5)`. At (p, −5) it is
(1/5)[[1, −2], [−2, 4]]. The two sum to the identity, and 5 times their
difference is H(p).

> **Implementation note.** The runtime computes the branch differential from
> the evaluated partial derivatives of χ, not from a reverse pass, and it
> divides by χ′(p, t), which the gap witness makes nonzero on the chart. The
> observations have the derivative rule `none`: the eigenvalue is an
> operand, not a smooth map, so no reverse pass opens them. The oracle
> theorems `VastitasOracle.SpectralRuntime.branch_some_iff`,
> `projector_idempotent`, `projector_trace_one`, `projector_eigen`,
> `projector_commutes`, `branchDifferential_implicit` and
> `branchDifferential_hellmann_feynman` state the definedness of the
> observations, the laws of P and the two forms of the differential, for an
> accepted spectrum and branch. No theorem states that P is symmetric for a
> symmetric field; the acceptance program tests it. The bridge theorem
> `VastitasBridge.Spectral.checked_branch_differential_implicit` states that
> an accepted branch differential is the derivative at p of every
> differentiable real branch λ with λ(p) = t and χ(x, λ(x)) = 0 near p. It
> takes λ as a hypothesis, and no theorem states that such a λ exists. The
> sum of the two eigenprojectors of the example is a property of that field:
> no observation forms a sum over the eigenvalues of a field.

## Operand checks

These rules apply to every call of a primitive of this chapter.

Rules:

- A call must have the number of operands that the binding fixes. Otherwise
  it is an error (`E_ARITY`).
- A value that is not a value of a family, such as an `Int`, in the place of
  a point or an eigenvalue is an error (`E_TYPE`).
- The point must be a point of the object of the spectrum or of the branch
  that the binding names. A point of another object is an error
  (`E_ENDPOINT`), even when the objects have one dimension.
- The eigenvalue must be a point of the line `L` that the binding names. A
  point of another object is an error (`E_ENDPOINT`).
- The source of the point must be a 0-dimensional smooth affine object, and
  the point and the eigenvalue must have one source. Otherwise it is an
  error (`E_ENDPOINT`).
- The type of a call names its result. A binding, a parameter or a result of
  another type is an error (`E_TYPE`), as for every value.

> **Implementation note.** The kernel checks every operand before code
> generation, and the generated code checks no identity: the kernel has
> checked the spectral pair and the gap witness of every declaration that a
> call reads. The message of an `E_ENDPOINT` for an operand of another
> object or of another source names the operand, the object that the
> binding expects and the one supplied. When the kernel finds no single
> operand at fault, as for a point whose source is not 0-dimensional, the
> message lists the types of the supplied operands instead.

## Scope of spectral observations

Spectral observations cover the endomorphism fields of free modules of rank
at most four on smooth affine objects, with entries that are polynomials
with rational coefficients. Every value is an exact rational number. A
branch is one finite chart D(g). Covers by several charts, charts whose
localization is not in A, image opens and splits of a cluster of eigenvalues
are outside the profile. So are the branch as a smooth function on an open,
derivatives of eigenprojectors and eigenvectors, higher derivatives,
Hermitian fields over the Gaussian rationals, physical units of eigenvalues,
and floating-point realizations. The language has no numerical eigensolver:
no primitive computes an eigenvalue, and a program supplies each eigenvalue
that it observes. No binding of this chapter reads a metric, a frame or a
physical dimension. A function body declares no free module, field,
spectrum or branch.
