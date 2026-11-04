# Presented affine geometry (Stage 2)

Historical Stage 2 adds a finite, checked profile of ordinary affine geometry
over QQ ([tracker #571](https://github.com/MGYamada/Vastitas/issues/571)). A
presented affine object stands for an exact QQ-algebra `QQ[g₁, …, gₙ]/I`. The
compiler parses its polynomial syntax. The independent Lean kernel expands it,
computes a reduced Gröbner basis and verifies that basis before any code is
generated. This chapter describes objects and morphisms over a base. Fiber
products and principal opens follow in later increments of the same tracker.

## Declaring the profile

```vast
pub indexed marker QQ;
pub indexed implementation AffineQQ(QQ, presented_affine(rational)) capabilities();
pub indexed classification AffineScheme { parents(); domain(AffineQQ); };
pub indexed family Over(object(AffineScheme), object(AffineScheme), object(AffineScheme))
    = token constraints(structural(0, 2), structural(1, 2));
pub indexed affine SpecQQ(AffineQQ) = spec[];
```

- **`presented_affine(rational)`** is a separate implementation
  representation. It has no descriptor capabilities and cannot back a plain
  `indexed global`. The Stage 1 `Point`, `Morphism` and `same_base` contracts
  never range over presented objects.
- **`structural(i, j)`** holds when index `i` and index `j` are canonical
  declared objects and `j` lies on the declared base chain of `i`. It compares
  object identity, never coefficient markers or shapes. A local object brand
  never satisfies it.

## Objects and bases

```vast
indexed affine D(AffineQQ) = spec[e] relations(e^2) over SpecQQ;
indexed affine S(AffineQQ) = spec[t] over SpecQQ;
indexed affine X(AffineQQ) = spec[t, x] relations(x^2 - t) over S by(t -> t);
indexed affine Origin(AffineQQ) = spec[] over S by(t -> 0);
```

- **The declaration.** `spec[…]` lists the coordinates and `relations(…)` the
  defining polynomials. `over B` names a declared base, and `by(b -> p, …)`
  gives the image of each of the base's coordinates in this object's ring,
  which defines the structure map `N → B`.
- **What the kernel checks.** Every base coordinate needs exactly one image.
  The images must send every relation of the base into this object's ideal,
  and the base must have the same coefficient marker.
- **Chains.** Base chains are finite (at most 16 objects) and acyclic. Each
  chain ends at an object without a base.
- **Identity.** Each declaration is one canonical object. Two separate
  declarations with the same presentation remain distinct. They become
  comparable only through an explicitly checked isomorphism, which a later
  increment adds.

Polynomial syntax uses `+`, `-`, `*`, unary `-`, `^` with a literal exponent,
decimal literals, `frac(n, d)` and parentheses. The `^` token exists only in
this syntax. Before expansion, the kernel bounds:

- degree and exponents to 16;
- literals to 64 digits;
- nesting to 64;
- each object to 16 coordinates and 32 relations;
- every intermediate polynomial to 512 terms;
- each check pass to a weighted work budget.

## Morphisms over a base

`Over<X, Y, S>` is a sealed `relative` family. It always has exactly three
presented-object parameters and the constraints `structural(0, 2), structural(1, 2)`.
A value of `Over<X, Y, S>` is a morphism `X → Y` that commutes with the structure
maps of both objects to `S`, written in pullback direction: it gives the image of
each of `Y`'s coordinates as a polynomial in `X`'s coordinates. A `T`-valued point
of `X` over `S` is an `Over<T, X, S>`.

```vast
indexed morphism p: Over<D, Line, SpecQQ> = pullback(t -> e);       // t ↦ ε
indexed morphism closed: Over<SpecQQ, D, SpecQQ> = pullback(e -> 0);
indexed morphism toX: Over<DS, X, S> = pullback(t -> 0, x -> e);
indexed morphism toS: Over<X, S, S> = structure;                    // along the chain
indexed morphism same_x: Over<X, X, S> = identity;

pub indexed primitive compose = relative_compose(Over);             // compose(after, before)
pub indexed primitive same = relative_equal(Over);                  // Bool
indexed primitive eps = relative_coefficient(Over, D, Line, t, e);  // Pair<Int> (num, den)
indexed primitive at = relative_int_point(Over, Line, SpecQQ);      // Int coordinates → point
indexed primitive view = relative_view(Over, S, SpecQQ);            // Over<X, Y, S> → Over<X, Y, SpecQQ>
```

**What the kernel checks for a declared morphism.**

- The pullback names each of the target's coordinates exactly once.
- The images are computed in the source's ring and stored as normal forms.
- Every basis element of the target maps into the source's ideal, with exact
  quotient identities.
- The triangle over `S` commutes.
- `identity` needs the same object. `structure` needs the target on the source's
  base chain.

**Typing of the primitives.**

- `compose(after, before)` substitutes in the written order. It requires the same
  base and matching middle objects, otherwise `E_ENDPOINT`.
- `same` compares two values of one exact type by their normal-form images.
- `relative_coefficient` reads one coefficient of one target coordinate's image
  as an exact rational.
- `relative_int_point` builds a rational point of a free object over a
  coordinate-free base from runtime `Int`s.
- `relative_view` changes the base only to one on the declared chain.

At runtime, a value of `Over<X, Y, S>` is an exact `AlgebraRuntime.Map`.
Generated programs import that runtime only when they use it.

The [example package](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/affine-geometry)
checks, builds and prints `42` after confirming:

- `p ≠ q` as D-valued points, while their composites with the closed point agree;
- the coefficient of ε in `p` is 1;
- `(t + 1)²` versus `t² + 1` for the two composition orders;
- the commuting triangle over `S`;
- that `sq` at the integer point 3 gives 9.

## Diagnostics

| Code | Meaning |
| --- | --- |
| `E_AFFINE_BASE` | Missing, cyclic or non-presented base; missing or extra base-coordinate images; a structure map that does not respect the base relations |
| `E_AFFINE_COORDINATE` | Unknown or duplicate coordinate; zero denominator |
| `E_AFFINE_RELATION` | A morphism does not respect the target's relations, or a stored basis or certificate fails verification (forged Core) |
| `E_ENDPOINT` | `compose` or `same` applied to morphisms whose objects or bases do not match |
| `E_LIMIT` | A bound above was exceeded |
| `E_PROTOCOL` | An algebraic form in a protocol-7 or protocol-8 envelope, or a malformed record |

## What is checked, tested and proved

- **Checked.** Each stored certificate has to satisfy exact polynomial
  identities: the basis is reduced and monic, cofactor combinations equal the
  basis, and every relation and every S-pair divides to zero with exact
  quotients and the standard-representation bound. Structure images must be
  normal forms whose pullbacks land in the ideal.
- **Proved.** The [verification reference](verification.md#exact-affine-algebra-checker-stage-2-571)
  lists the oracle theorems. Successful verification establishes those
  identities. Accepted declarations have bounded, presented chains, and the
  Stage 1 sealed families exclude presented objects. Accepted morphisms carry
  the identities listed in the previous section. Every new primitive is total
  and typed, and its result agrees with the erased runtime operation.
- **Tested.** Kernel regressions cross-check bases and normal forms against an
  independent Python model. Rust tests cover source, wire and native paths.
- **Not yet claimed.** The meaning of these identities in `MvPolynomial` and
  `Spec`, and the canonicity of normal forms, belong to the mathlib bridge
  increments of #571. ZZ or F_p coefficients, gluing, smooth spectra and
  module presentations are outside this profile.
