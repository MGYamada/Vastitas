# Exact finite spectral pairs: rank-two reference

This is an **external Python reference** for the initial exact examples of
[#337](https://github.com/MGYamada/Vastitas/issues/337), under
[ADR 0001 §§3–4](adr/0001-mathematics-first-stdlib.md) and
[historical Draft §10](design/differentiation-spectral.md#10-eigen-as-spectral-geometry).
It checks concrete rational calculations. It is not a public `eigen` implementation,
a Lean proof, accepted Vastitas Core, numerical eigensolver, or completion of #337
or the stdlib implementation tracker [#160](https://github.com/MGYamada/Vastitas/issues/160).

## Supported descriptor and arithmetic

The input is an exact endomorphism `H: V -> V` on a declared free `V=QQ^2`,
with a named environment, coefficient base, space, ordered coordinate basis
identity, map identity and revision. Source and target must be the same frame.
Integers are converted to `Fraction`; floats, bools, complex machine numbers,
noncommutative coefficient profiles and other dimensions are rejected.

The pair retains:

```text
chi_H(t) = det(t I - H)
A_H      = QQ[t]/(chi_H), with QQ basis (1,t)
Sigma_H  = Spec A_H                         (presentation only)
M_H      = QQ^2 with 1-action I and t-action B
P: M_H -> V, invertible, with H P = P B.
```

`Evidence.algebra` presents the characteristic scheme. Its separate module
action and pushforward identification recover the original H. `propose` uses
`B=H, P=I`; the verifier also accepts explicitly changed module coordinates.
The associated sheaf `F_H = tilde(M_H)` and projection to `Spec(QQ)` are the
mathematical interpretation of this presentation, not implemented Scheme or
sheaf objects. No metric, conjugation, root ordering or eigenvectors enter it.

[finite_spectral_reference.py](../scripts/finite_spectral_reference.py) reuses
[shared Poly](../scripts/rational_polynomial_reference.py) and the existing
rational 2×2 helpers in [metric_free_reference.py](../scripts/metric_free_reference.py).
Only its scalar/matrix arithmetic is reused, not that module's real-plane
geometric profile. The tests reuse shared polynomial substitution/evaluation.
No new matrix class, polynomial representation, optional CAS, numerical library
or general matrix/module algebra is added. `QuadraticAlgebra` is a small
monic-degree-two remainder adapter over shared Poly. It makes no field claim;
normal forms have degree less than two, including nonzero nilpotents.

Polynomial elements have one slot interpreted under an explicitly supplied
generator name. Their structural equality compares presentations. It is not
nominal equality of independently declared rings, schemes or bases. Subject
identities are fixture data, not authenticated environment declarations.

## Separate verification obligations

`verify(expected_subject, evidence)` binds the entire independent request and
then checks these obligations separately:

1. **Characteristic scheme:** expand `(t-a)(t-d)-bc` and compare every coefficient
   and the generator role. The producer uses trace/determinant coefficients;
   the checker does not call it. A mocked incorrect producer is rejected.
2. **Cayley–Hamilton:** evaluate the entire claimed polynomial on the original
   H using exact matrix powers and require zero.
3. **Quotient module:** require the identity action for 1 and `chi_H(B)=0`.
   The action of a representative is its remainder evaluated at B. The defining
   ideal acts by zero; tests separately exercise unit, addition, vector
   linearity, composition and independence of the polynomial representative.
4. **Identified pushforward:** require `det(P) != 0` and `H P = P B`.
   A singular comparison cannot hide a missing part of the original operator.

These checks are not interchangeable. For H=0, the wrong polynomial `t^2+t`
still satisfies Cayley–Hamilton. For H=HJ, erasing B to zero still defines a
unital module over `QQ[t]/t^2`; recovery of H rejects it. Replacing M by the
regular module passes the quotient relation for H0 but also fails recovery.

The two computational routes share Python and exact arithmetic helpers. Their
agreement and the finite test family are not independent verification of those
helpers or a universal formal proof. Constructing a frozen dataclass or copying
an ID does not grant authority; consumers must call the relevant verifier.

## Same scheme, different modules

| Operator | Characteristic algebra | Action of epsilon=t | Module over A=QQ[epsilon]/epsilon^2 |
| --- | --- | --- | --- |
| H0=0 | A | zero | `(A/(epsilon))^2` |
| HJ=[[0,1],[0,0]] | A | nonzero, square zero | A, with an explicit comparison |

The regular representation of multiplication by t on A, in basis `(1,t)`, is
`[[0,0],[1,0]]`. The swap matrix supplies the isomorphism to HJ. The verifier
requires that actual invertible intertwiner before accepting `M_H ~= A`.
For H0 no such intertwiner can exist: `0*U=U*HJ` with invertible U would force
HJ=0. Its module is not a line bundle over A. The characteristic scheme is
still nonreduced even though its action on M0 kills epsilon. Substituting the
annihilator `(t)` for the characteristic ideal `(t^2)` is rejected.

The tests also shift the repeated root to `a=3/7`, retain an off-diagonal as
small as `10^-60`, and keep the nonzero class `t-a` while its square vanishes.
Root-set reduction is rejected by the exact monic degree-two contract.

## Similarity, specialization and scalar extension

`check_similarity` takes two independently bound pairs and an explicit
`U: V_right -> V_left`. It checks invertibility, compatible named coefficient
bases, `H_left U = U H_right`, and the characteristic algebra. It does not
identify the two nominal map/basis identities. Tests check higher polynomial
actions as well as H itself, and reject reversed/singular or false comparisons.

The polynomial families `diag(s,-s)` and `[[s,1],[0,-s]]` both have
`chi=t^2-s^2`. Specializing the shared QQ[s,t] polynomial agrees with computing
the descriptor after rational specialization, including s=0. For s nonzero
the explicit comparison `[[1,1/(2s)],[0,1]]` is valid; at zero the first module
is M0 and the second is MJ. Their common nonreduced scheme survives; the
comparison with a pole does not extend. This is a finite family fixture, not
an implementation of arbitrary parameter rings or smooth eigenbranches.

The separate `ScalarExtension` adapter supports **only the constant inclusion**
`QQ -> S=QQ[u]/q(u)` for a supplied monic quadratic q. It retains S, embeds
every characteristic coefficient, and retains the entrywise H action on S²
in the identified V basis. The checker recomputes the determinant over S,
compares the embedded characteristic, verifies the actual action, and evaluates
Cayley–Hamilton on both S-basis vectors. `extended_act` applies `a(u)+b(u)t`
to genuine S-valued vectors. It does not base-change eigenvector kernels.

Positive cases include S=QQ(sqrt(2)): `H=[[0,2],[1,0]]` has polynomial `t^2-2`,
and the supplied vectors `(u,1)` and `(-u,1)` have eigenvalues u and -u. Their
determinant `2u` is a unit, checked against inverse `u/4`. No roots are computed
numerically. H0/HJ remain distinct after this extension and after extension to
the dual-number coefficient algebra `QQ[u]/u^2`. Relations, nonrational
coefficient action and multiplication are checked exactly. General ring maps,
arbitrary exact fields and locally free bundles remain deferred.

An explicitly supplied nonzero rational eigenvector may be checked as an
optional observation. A canonical vector/frame or smooth-branch tag is
unsupported. The H0 regression exhibits an automorphism (the swap) that fixes
H0 but moves the chosen line, so an arbitrary coordinate choice cannot be
promoted to a canonical one.

## Connection to #247: Bloch/Fermi versus the operator module

The permanent regressions use the existing shared polynomial operations to
check the SSH equation, without adding another Laurent implementation:

```text
H(z) = [[0, v+w/z], [v+w*z, 0]],        z is invertible
z P(z,E) = z E^2 - (v z+w)(v+w z).
```

At each tested nonzero rational z, the exact 2×2 spectral descriptor agrees
with this polynomial after specialization. For v=w=1 and E=0 the cleared
equation is `-(z+1)^2`. The quotient `QQ[z]/(z+1)^2` already has z invertible,
with inverse `-z-2`; it presents the same Laurent Fermi fiber. Its epsilon=z+1
is nonzero with square zero. Only an invertible z factor is cleared, and no
claim is made about a z=0 boundary or general ideal saturation.

There are **two different fibers** here. Fixing E=0 gives a double point in z.
Fixing z=-1 gives H=0 and the characteristic algebra `QQ[t]/t^2` in energy.
In the latter, the physical two-component operator module has zero t-action,
whereas the structure sheaf has nonzero regular t-action. Thus #247's finite
free `pi_* O_Bloch` with energy basis `(1,E)` is not a universal replacement
for #337's `pi_* F_H ~= V`. Even identical characteristic schemes need their
operator-associated modules.

The broader Laurent/fan work remains in
[#247](https://github.com/MGYamada/Vastitas/issues/247) and the separate SSH
reference [PR #274](https://github.com/MGYamada/Vastitas/pull/274), which was
still an unmerged draft when this increment was prepared. This increment
does not import/copy that PR's Laurent or dual-number types or depend on its
merge. The tests establish a compatible concrete consumer at the exact
presentation level, not production interoperability between two stdlib APIs.
An additional preparation-time comparison against #274's pinned head
`d1ddd40be1472d55de10c2821d1f8acec8293d05` agreed on all 18 rational fibers
and on the coordinate change between its dual-number normal form and the
quadratic quotient here. That cross-branch comparison is not a CI dependency;
the permanent tests retain the explicit shared-polynomial equations above.

## Reproduction and remaining obligations

From the repository root, with Python's standard library only:

```sh
python3 -S scripts/demo_finite_spectral_reference.py
python3 -m unittest discover -s scripts -p 'test_finite_spectral_reference.py' -v
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/check_boundaries.py
git diff --check
```

The 28 focused tests include 81 rational matrices, 18 rational SSH fibers,
explicit similarity and scalar-extension witnesses, the repeated-root family,
and the four required negative classes: characteristic-only identification,
nilpotent erasure, reduction to root sets, and unjustified canonical choices.
They also reject stale identities/revisions, coefficient/basis mismatch,
forged actions, singular pushforwards and inexact inputs. Existing CI discovers
the suite through its current `test_*.py` pattern.

Validation on base `0a1062845dc58f030bc946cf52598db81a5bc9f2`: all 28 focused
tests passed; the full Python suite ran 398 tests, with 397 passes and one
existing live compiler/kernel integration skip because those binaries were not
built. The `-S` demo, dependency-boundary checker and whitespace check passed.
No Rust or Lean changes/build/proof completion are claimed.

| Layer | Established here / remaining work |
| --- | --- |
| Python reference | Exact instance calculations and mutation rejections in the stated finite profile. No general soundness theorem follows from test counts. |
| Mathematical descriptor | The stated characteristic algebra, quotient action and identified pushforward; sheaf semantics remain a specification. No generic schemes, modules or matrix theory are introduced. |
| Lean | Formalize the actual arithmetic/checker and prove acceptance implies the specified characteristic/module facts, similarity and base change. Under #285, distinguish mathematical definitions, implementation soundness and pinned-mathlib correspondence. No new Lean code, axiom or completed proof is supplied. |
| Actual accepted Core | Authenticate nominal endpoints, coefficient maps, bases, revisions and evidence from the actual environment; compose existing Domain Checkers and Ownership/Borrow; bind results to the exact returned Core and test forged IR. None of this is established by Python fixture labels. No ninth checker. |
| Numerical/native realization | Optional eigenvalue observations require separate scalar, residual/enclosure, gauge/ordering, error and refinement contracts. No LAPACK call, floating eigensolver, tolerance, performance result or native proof is added. |

SVD, arbitrary dimensions, generic ideal equality, automatic eigenbasis choice,
global smooth eigenbranches and finite-locally-free gluing remain outside this
reference. CS/MS/CF and the existing checker architecture are unchanged.
