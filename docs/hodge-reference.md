# Exact finite pointwise Hodge reference (#375)

This is a **Python reference calculator and independent candidate verifier** for
[#375](https://github.com/MGYamada/Vastitas/issues/375). It adds no public Vastitas
syntax, registered stdlib operation, Lean proof, Core primitive, numerical
adapter, or physical guarantee. The issue remains open. This first stage uses
exact rational coordinates on real Euclidean three-space and real Lorentz
four-space. It does not implement differential geometry or global Hodge theory.

## Run and inspect

Python 3.10 or later; standard library only:

```sh
python3 scripts/demo_hodge_reference.py
python3 -m unittest discover -s scripts -p 'test_hodge_reference.py' -v
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/check_boundaries.py
```

The demo emits JSON with exact rational strings and expected rejection codes;
it exits successfully only when every expectation passes. This is a demo report,
not a compiler wire format or proof certificate. Existing CI's Python test
discovery runs the new regressions without workflow changes.

| File | Responsibility |
| --- | --- |
| [hodge_reference.py](../scripts/hodge_reference.py) | Explicit finite inputs, exterior/sign-line data, checked metric evidence, star calculator, defining-identity verifier, derived cross product, active linear actions |
| [test_hodge_reference.py](../scripts/test_hodge_reference.py) | Independent sign tables, square laws, 48 signed permutations, rational rotation/boost, nonorthonormal metrics and evidence mutations |
| [demo_hodge_reference.py](../scripts/demo_hodge_reference.py) | Reproducible exact examples and expected failures |

The implementation reuses the strict `rational` conversion from
`rational_polynomial_calculus`, `Invalid` from `rational_polynomial_reference`,
and the existing reference identifier validator. Arithmetic uses the same
`fractions.Fraction` foundation. The older #264 reference's frame and matrix
operations are intentionally two-dimensional; their accepted fragment is not
widened. The few private rank-three/four matrix and minor operations here do not
create a general numerical linear-algebra library. No native BLAS or floating
metric is treated as exact mathematical evidence.

## Explicit premises and exact fragment

`Frame` requires rank, environment/object/base/fiber/model identities and revision,
named coefficient identity, the supported `Q-to-R-pointwise/v1` interpretation,
and ordered basis/dual-basis identities. Its basis defines a formal coordinate
basis of the declared finite free real fiber. It is not a certificate that an
arbitrary bundle is locally free. The nominal fiber token does not provide
transport to another point. Same-sized arrays do not identify fibers or bases.

`Metric` is a selected, named symmetric real bilinear form with a rational Gram
matrix and revision. It is distinct from the native protocol-8 diagonal Hermitian
metric. Hodge operations require all three separately supplied evidence records:

| Evidence | Exact check against the independently selected metric |
| --- | --- |
| Nondegeneracy | Candidate inverse `B` must satisfy both `G B = I` and `B G = I` |
| Signature | Invertible rational `A` and nonzero rational diagonal `d` must satisfy `A^T G A = diag(d)`; `q` must equal the number of negative entries |
| Volume | Positive rational `v` must satisfy `v^2 = abs(det G)` |

Supported signatures are `(n,q)=(3,0),(4,1),(4,3)`. Nondegeneracy alone implies
neither positivity nor a signature. Inverse, diagonalizer, signature and volume
are never synthesized by a star call. No orientation is selected by a metric.
All evidence binds to the entire metric subject, including matrix entries and
all frame/coefficient identities. These string identities are finite reference
labels, **not authentication by a compiler environment**.

Normalized Hodge star need not preserve rational coefficients. For
`G=diag(4,1,1)` the supplied volume is `2`, and `star(dx wedge dy)=dz/2` is
accepted. For `G=diag(2,1,1)` the result would be `dz/sqrt(2)`; this reference
rejects the profile with `COEFFICIENT_EXTENSION_REQUIRED`, even for a zero input.
It does not round, pretend the sign line supplies the missing volume magnitude,
or silently switch to a densitized operator. Algebraic coefficient extensions
and distinctly typed density/volume-line alternatives remain future work.

## Conventions and verification

Forms are rational coefficients of increasing dual-basis wedges, with no
factorial normalization. For `B=G^-1`, the induced pairing of basis k-forms is
the corresponding minor `det(B[I,J])`. The declared convention is

```text
alpha wedge star(beta) = <alpha,beta>_g vol_(g,orientation)
vol_(g,orientation) = orientation.sign * sqrt(abs(det G)) * dx0 wedge ... wedge dx(n-1)
star^2 on degree k = (-1)^(k(n-k)+q), where q counts negative squares
```

The calculator uses complementary multi-indices. `verify_star` does **not** call
the calculator: it tests the defining wedge equation against every degree-k
basis form, after checking the candidate's exact fiber, degree and twist. The
common inverse-minor pairing is checked against independent hand-written sign
tables and nonorthonormal examples. This is an independent candidate-checking
path, not an independently verified arithmetic implementation. In particular,
negating the whole star preserves its square but fails the defining equation.

For `G=diag(-1,1,1,1)` and orientation `dt wedge dx wedge dy wedge dz`:

| Input | Star |
| --- | --- |
| `dt wedge dx` | `-dy wedge dz` |
| `dt wedge dy` | `dx wedge dz` |
| `dt wedge dz` | `-dx wedge dy` |
| `dx wedge dy` | `dt wedge dz` |
| `dx wedge dz` | `-dt wedge dy` |
| `dy wedge dz` | `dt wedge dx` |

All six have square `-1`. Euclidean four-dimensional signs, which would give
square `+1` on 2-forms, are rejected as candidates for this Lorentz metric;
Euclidean rank four is not an admitted production profile of this reference.
The opposite `(+,-,-,-)` profile is separately certified and tested.

## Orientation line, cross product and ownership

`OrientationLine(frame)` represents the determinant-**sign** character, not the
determinant line's volume magnitude. Twisted form coordinates are stored relative
to the generator induced by the explicitly ordered basis. That coordinate
presentation does not choose a geometric orientation for the user. The
orientation-free `star_twisted` attaches this line; on twisted input it removes
the line using the canonical sign-character identity `or(V)^2 = 1`.

`Orientation(frame,+1/-1)` is a separately supplied trivialization. Reversing it
negates `star` and the displayed axial components but does not change the twisted
object. `display_twisted` returns components; it does not cast an `AxialVector`
to a `PolarVector`. The latter types cannot be interchanged in `cross_twisted`.

The cross product is exactly the ordinary composition

```text
sharp(g, star_twisted(g, flat(g,a) wedge flat(g,b)))
```

and returns an `AxialVector`. The standard basis gives `ex cross ey = ez` in the
positive display, with antisymmetry and rational non-basis examples checked.
Active `FrameAutomorphism` uses `Q` on polar vectors, `Q^-T` on covectors and
`sign(det Q)` on each orientation-line factor. For isometries this yields
`cross(Qa,Qb) = det(Q) Q cross(a,b)`. All 48 signed permutations, a rational
proper rotation, and a rational Lorentz boost are tested. Isometry is checked
by `Q^T G Q=G`; a Euclidean time-space rotation is rejected for Minkowski `G`.
These are active actions on a single declared fiber, not a general passive
change-of-chart, bundle gluing, or a claim about physical transformations.

| Design owner | Reference alignment and remaining boundary |
| --- | --- |
| #246 `std::algebra::exterior` | Wedge, degree, sign-line tensor law and active exterior actions are metric-free; no Clifford/CAR implementation is added |
| #264 `std::geometry::metric` | Selected symmetric form, explicit inverse evidence, flat/sharp; flat is meaningful without nondegeneracy, sharp is not; no change to metric-free AD |
| #375 `std::geometry::hodge` | Derived pointwise star, explicit normalization/signature, twisted and selected-orientation representations |
| #372 `nature::vector3d` | Mathematical cross composition and axial behavior are available as reference examples; no physical-space/unit identification or registered facade is claimed |
| #373 `nature::relativity` | Explicit Lorentz sign convention and exact boost compatibility; no observer, clock, spacetime model or physical correctness is inferred |

## #375 acceptance mapping and status

| Issue obligation | Evidence in this first stage | Still open |
| --- | --- | --- |
| Oriented Euclidean rank three, cross, square law | `test_euclidean_full_basis_table_and_orientation`, `test_cross_is_flat_wedge_star_sharp_with_axial_type`, all-degree square tests | Lean theorem and actual Core integration |
| Orientation reversal and axial reflection | Twisted/display tests, all 48 signed permutations, explicit rejection of a polar reflection rule | Global orientation-line/bundle naturality |
| Correct Lorentz profile | Independent six-entry table, both Lorentz sign conventions, square laws in every degree, exact boost | Lean proof and public implementation |
| Reject missing/mismatched premises and silent polar/axial conversion | Schema, input, evidence, output and identity mutations; separate types and explicit displays | Bundle gluing is unsupported, not validated by a pointwise example |
| Do not infer global analytic or physical guarantees | Explicitly limited API and scope; no such proof/claim admission path | Stokes/Hodge decomposition/clock hypotheses are outside this reference |
| Transparent std ownership and facade expansion | Composition is visible above; ownership table distinguishes the mathematical maps | Registered Vastitas facade exports and accepted-Core equivalence proofs |
| Exact coefficient/density amendment | Nonorthonormal rational-volume and off-diagonal positive examples; reject `diag(2,1,1)` as falsely rational | Scalar extension and distinctly typed densitized duality |

The regression suite has 20 test methods, with basis, signature and action loops
inside them. Test counts are finite observations, not universal Lean proofs.
Reference calculations, Lean-kernel mathematics, source-to-Core implementation,
native refinement and physical interpretation remain separate deliverables.
