# Presented affine geometry (Stage 2)

Historical Stage 2 adds a finite, checked profile of ordinary affine geometry
over QQ ([tracker #571](https://github.com/MGYamada/Vastitas/issues/571)). A
presented affine object stands for an exact QQ-algebra `QQ[g₁, …, gₙ]/I`. The
compiler parses its polynomial syntax. The independent Lean kernel expands it,
computes a reduced Gröbner basis and verifies that basis before any code is
generated. This chapter describes the object declarations that are available
now. Maps, fiber products and principal opens follow in later increments of the
same tracker.

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

## Diagnostics

| Code | Meaning |
| --- | --- |
| `E_AFFINE_BASE` | Missing, cyclic or non-presented base; missing or extra base-coordinate images; a structure map that does not respect the base relations |
| `E_AFFINE_COORDINATE` | Unknown or duplicate coordinate; zero denominator |
| `E_AFFINE_RELATION` | A stored basis or certificate fails verification (forged Core) |
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
  Stage 1 sealed families exclude presented objects.
- **Tested.** Kernel regressions cross-check bases and normal forms against an
  independent Python model. Rust tests cover source, wire and native paths.
- **Not yet claimed.** The meaning of these identities in `MvPolynomial` and
  `Spec`, and the canonicity of normal forms, belong to the mathlib bridge
  increments of #571. ZZ or F_p coefficients, gluing, smooth spectra and
  module presentations are outside this profile.
