# Exact real-plane metric reference (#264)

This is an executable **Python reference with regression tests** for the thin
metric layer in [#264](https://github.com/MGYamada/Vastitas/issues/264). It is not
Vastitas execution, a Lean theorem, production stdlib registration, a new AD
primitive, or a new Domain Checker. General Riemannian geometry is outside its
scope. No release or completion condition is added.

The implementation baseline is main `d783b5a6e393214a54cb408501963b1e42a7be94`.
It reuses `Poly`, exact differentiation and arithmetic from the existing
[symplectic reference](symplectic-reference.md), without changing that verifier.
The four-variable arithmetic engine is restricted to its subring `Q[x0,x1]`:
every public polynomial boundary rejects any nonzero exponent of `x2` or `x3`.
This is an arithmetic implementation detail, not a four-dimensional geometry
or an extension of the symplectic verifier's accepted profile.

## Run

Python 3.10 or later; standard library only, using arbitrary-precision integers
and `fractions.Fraction`. There is no SymPy/runtime dependency, numeric tolerance,
finite differencing, expression parser, or approximate eigenvalue calculation.

```sh
python3 scripts/demo_metric_reference.py
python3 -m unittest discover -s scripts -p 'test_metric_reference.py' -v
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/check_boundaries.py
```

The demo prints JSON with exact rational strings, separate cotangent/metric/
gradient checks, and expected negative cases. It exits `0` only when every
declared expectation matches, including rejection expectations. These exit
codes are for the demo, not a compiler acceptance or certificate wire protocol.
Existing CI's Python discovery includes the regressions automatically.

| File | Responsibility |
| --- | --- |
| [metric_free_reference.py](../scripts/metric_free_reference.py) | Named frames and fibers, polynomial differentiation, metric-free reverse cotangent pullback, rational coordinate changes |
| [metric_reference.py](../scripts/metric_reference.py) | Selected symmetric forms, inverse/positivity evidence, flat/sharp, derived gradient, independent metric and gradient transport checks |
| [demo_metric_reference.py](../scripts/demo_metric_reference.py) | Runnable two-dimensional example and expected failures |
| [test_metric_reference.py](../scripts/test_metric_reference.py) | Exact examples, symbolic identities, finite coordinate grid, variance and evidence mutations |

The metric-free module does **not** import the metric module. A fresh-process
test checks this dependency separation. Neither `differential` nor
`cotangent_pullback` takes a metric, finds a default, or consults a registry.

## Mathematical fragment

Every named geometric object is a real plane with a selected global ordered
coordinate frame and its dual. Scalar functions belong to `Q[x,y]`, interpreted
as smooth functions on **R^2** through `Q -> R`. Polynomial maps have two such
components. Executable basepoints and vector/covector components are rational;
this does not change the mathematical domain to a manifold over `Q`.

Metrics here are constant symmetric rational 2-by-2 matrices, interpreted as
real bilinear forms on the entire declared plane. Coordinate changes are
invertible rational linear maps `x = A u` on the **same** nominal object/base/model.
They have no translations or nonlinear chart domains. General polynomial maps
are available only for testing metric-free pullback; they do not manufacture
nonconstant metrics or general coordinate changes.

All components are columns. Covectors act by `alpha^T v`; this is the canonical
dual pairing and introduces no metric. At the actual output `F(p)`,

```math
d f_p = (\partial_1 f(p),\partial_2 f(p))^T,
\qquad F_p^*(\eta)=J_F(p)^T\eta.
```

The pullback rejects a seed over any other point/object/frame, even when its
shape and numbers match. `gradient(f,p,using=g,evidence=e)` is only the ordinary
composition `sharp(FiberMetric(g,p), differential(f,p), e)`.

The three coordinate transformation rules are checked separately:

| Data | Rule for `x = A u` | Independent check |
| --- | --- | --- |
| Differential / cotangent | `alpha_u = A^T alpha_x` | `check_cotangent_transport`, also compared with symbolic differentiation of `f(Au)` |
| Selected metric | `G_u = A^T G_x A` | `check_metric_transport`, retaining metric name/revision and changing the frame explicitly |
| Gradient / tangent | `v_u = A^-1 v_x`, equivalently `A v_u = v_x` | `check_gradient_transport`, rechecking both sharp results and their evidence against independently supplied inputs |

The last checker receives the original metric, covector, coordinate change and
source point independently of the two proposed result records. It reconstructs
both expected metric fibers and the pulled covector. A record cannot establish
its own correctness merely by declaring a plausible subject or result.

## Exact example and failures

For `f=x^2+xy+3y^2`, `p=(1,2)`, and `A=((1,1),(0,1))`, the source point is
`u=(-1,2)`, so `A u = p`.

| Quantity | Exact result |
| --- | --- |
| `df_p` | `(4,13)` |
| `grad_g f`, `G=diag(2,3)` | `(2,13/3)` |
| `grad_h f`, `H=((2,1),(1,2))` | `(-5/3,22/3)` |
| `d(f o A)_u = A^T df_p` | `(4,17)` |
| `G_u = A^T G A` | `((2,2),(2,5))` |
| `grad_(G_u)(f o A)` | `(-7/3,13/3)` |
| Pushed gradient | `A(-7/3,13/3) = (2,13/3)` |
| Incorrect vector transformation of `df` | `A^-1(4,13) = (-9,13)`, rejected |

The last failure is observable under the canonical pairing: for the source
tangent `(0,1)`, the correct pairing is `17` in either frame; the wrong covector
gives `13`. Passing a `Cotangent` directly to tangent transport is also rejected
by its variance tag, including in orthonormal coordinates where numbers could
otherwise hide the mistake.

Additional tests include rational coefficients and points, nonlinear polynomial
map pullback/composition, symbolic chain-rule identities and a finite grid of
rational coordinate changes (including orientation reversal), functions,
points and metrics. Metrics on both endpoints may be added or swapped without
changing `df` or cotangent pullback. Even an unrelated degenerate form does not
block these metric-free operations.

## Nondegeneracy and positivity are distinct

`Metric` checks exact symmetry but does **not** assume invertibility or positivity.
`flat` is valid for a degenerate symmetric form. A `NondegenerateEvidence`
candidate supplies an inverse `B`; the checker independently tests **both**
`G B = I` and `B G = I`. `sharp` requires this evidence explicitly.

`RiemannianEvidence` adds the leading minors `(G00, det(G))`. The checker
recomputes both, verifies the bound inverse evidence, and requires both to be
strictly positive (the two-dimensional real Sylvester criterion). For a
symmetric `G=((a,b),(b,c))` with `a>0`, the underlying algebraic argument is

```math
(s,t)G(s,t)^T = a(s+(b/a)t)^2 + (\det G/a)t^2.
```

This is a statement about the **constant matrix**, not a finite point sample
purporting to establish global positivity. Its formal soundness theorem over
all real tangent vectors remains a Lean obligation.

| Form | Flat | Inverse evidence / sharp | Riemannian refinement |
| --- | --- | --- | --- |
| `diag(1,0)` | Available; `(0,1)` lies in its kernel | Rejected: determinant exactly zero; a forged inverse also fails | Unavailable |
| `diag(1,-1)` | Available | Accepted: inverse is itself | Rejected: negative quadratic value on `(0,1)` |
| `diag(-1,-1)` | Available | Accepted | Rejected despite positive determinant: first leading minor is negative |
| `diag(2,3)` | Available | Accepted | Both leading minors positive |

There is no tolerance-based promotion from nondegenerate to positive definite.
The reference does not add a general signature classifier or variable-metric
positivity decision procedure.

## Identity, evidence, and trust

The independently supplied `FiberMetric` is matched against the **whole**
immutable evidence subject, not just dimensions, a printed name, or the matrix:

| Index | Bound data |
| --- | --- |
| Environment / geometry | Environment snapshot, nominal object, geometric base, model and revision, fixed real interpretation |
| Basis | Chart, tangent frame and dual cotangent frame identities, ordered coordinate labels |
| Basepoint | Exact rational coordinates in that exact frame |
| Selected metric | Metric ID, revision and full rational Gram matrix |

Basepoints in this restricted global-coordinate model are exact values: equal
coordinates in the same frame denote the same point; the same coordinates on
another nominal object do not. A coordinate change explicitly relates their
different frame representations. No coefficient ring marker substitutes for a
geometric base object.

Two metrics with identical matrices and different IDs cannot reuse each other's
evidence. Stale revisions, changed matrices, different bases/frames/model
snapshots and different basepoints are rejected. Evidence for a transformed
metric must be checked for its new presentation. These fiber-bound certificates
are deliberately conservative: one may recheck the same constant inverse at a
new point, but cannot silently replay the old point's result record.

`FlatResult` and `SharpResult` retain the entire selected subject, argument and
result; `SharpResult` also retains the inverse evidence. The contained vector
or covector is an ordinary geometric value. Extracting that value does not
transfer the record's authority or turn evidence about `g` into evidence about
`h`. Vectors and covectors remain distinct types without automatic coercion.

This is an in-process reference API, not a hostile-code boundary or an
authenticated namespace system. The caller must supply the expected identities
independently; strings do not prove ownership, chart provenance or accepted
Core identity. If a caller constructs a newly bound candidate and the checker
recomputes all algebra for the new subject, that is a fresh reference check,
not an authorization transfer. Python object tampering and production wire
decoding are outside this model. The reused arithmetic and Python runtime are
part of the reference's trusted implementation, not Lean-checked machinery.

## Future Lean and accepted-Core obligations

Keep these obligations separate from the finite regression results:

1. **Metric-free differential/pullback.** Formalize the rational polynomial
   representation over `R`, its derivative and the canonical dual map. Prove
   correct basepoints, polynomial chain rule and reverse composition without
   any metric premise. Establish invariance under adding/replacing unrelated
   metric declarations in the *actual* elaboration environment.
2. **Musical maps.** For the independently selected constant symmetric `G`,
   prove that both inverse identities justify sharp and both inverse laws.
   Separately prove the real positive-definiteness refinement from the checked
   minors. Bind each result to the correct metric, frame and basepoint. Prove
   `sharp_(A^T G A)(A^T alpha) = A^-1 sharp_G(alpha)` for invertible `A`.
3. **Actual acceptance and denotation.** A future implementation must import
   the actual kernel definitions and connect successful checks to the exact
   environment, source occurrence, returned Core term and audit trace. For
   that occurrence, its polynomial/metric denotation must equal the requested
   subject; a parallel Python record or a separately checked lookalike Core
   is insufficient. AD correctness must remain independent of the optional
   musical-map evidence. Apply the existing Fiber/Basepoint, Linearity,
   Equality and other relevant jurisdictions and independent ownership checks
   from #184; no extra checker or metric privilege is proposed.

Schematically, the future metric-free route must establish
`denote(actual_pullback_core)(p,eta) = D(denote(F))_p^*(eta)` for a seed at the
actual `F(p)`. The selected sharp route additionally needs
`denote(actual_sharp_core)(alpha) = inverse(G) alpha` for that exact `G` and
certified fiber. These are future correspondence statements, not current
theorems or results of running this script. The tests do not prove compiler
soundness, native refinement, all-input Python correctness, or any general
smooth/geometric theorem. No connection, curvature, geodesic, Hodge operator,
default Euclidean metric, implicit adjoint or new AD primitive is introduced.
