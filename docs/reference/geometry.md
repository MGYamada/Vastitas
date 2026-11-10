# Mathematical geometry reference models

These independent exact models exercise plane metrics, symplectic maps and first variations. Each has its own hypotheses, verifier and regression examples.

<a id="metric-reference"></a>

## Exact real-plane metric reference (#264)

This is an executable **Python reference with regression tests** for the thin
metric layer in [#264](https://github.com/MGYamada/Vastitas/issues/264). It is not
Vastitas execution, a Lean theorem, production stdlib registration, a new AD
primitive, or a new Domain Checker. General Riemannian geometry is outside its
scope. No release or completion condition is added.

The implementation baseline is main `d783b5a6e393214a54cb408501963b1e42a7be94`.
It reuses `Poly`, exact differentiation and arithmetic from the existing
[symplectic reference](#symplectic-reference), without changing that verifier.
The four-variable arithmetic engine is restricted to its subring `Q[x0,x1]`:
every public polynomial boundary rejects any nonzero exponent of `x2` or `x3`.
This is an arithmetic implementation detail, not a four-dimensional geometry
or an extension of the symplectic verifier's accepted profile.

### Run

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
| [metric_free_reference.py](https://github.com/MGYamada/Vastitas/blob/main/scripts/metric_free_reference.py) | Named frames and fibers, polynomial differentiation, metric-free reverse cotangent pullback, rational coordinate changes |
| [metric_reference.py](https://github.com/MGYamada/Vastitas/blob/main/scripts/metric_reference.py) | Selected symmetric forms, inverse/positivity evidence, flat/sharp, derived gradient, independent metric and gradient transport checks |
| [demo_metric_reference.py](https://github.com/MGYamada/Vastitas/blob/main/scripts/demo_metric_reference.py) | Runnable two-dimensional example and expected failures |
| [test_metric_reference.py](https://github.com/MGYamada/Vastitas/blob/main/scripts/test_metric_reference.py) | Exact examples, symbolic identities, finite coordinate grid, variance and evidence mutations |

The metric-free module does **not** import the metric module. A fresh-process
test checks this dependency separation. Neither `differential` nor
`cotangent_pullback` takes a metric, finds a default, or consults a registry.

### Mathematical fragment

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

### Exact example and failures

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

### Nondegeneracy and positivity are distinct

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

### Identity, evidence, and trust

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

### Future Lean and accepted-Core obligations

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

<a id="symplectic-reference"></a>

## Exact polynomial symplectic reference (#211)

This is an **executable Python reference verifier with regression tests** for a
small fragment of [#211](https://github.com/MGYamada/Vastitas/issues/211).
It is not Vastitas execution, a Lean proof, production std registration, or an
additional Domain Checker. No release version or new completion condition is
assigned. The compiler, kernel, oracle and stdlib are unchanged.

The implementation baseline is main
`f56edd4be0010312c24a13bd66a6e43521638a19`. That tree and the related PR search
contained no symplectic reference implementation. This follows the existing
`scripts/graph_reference.py` / `test_graph_reference.py` convention; the existing
Python test discovery picks up the new tests without a workflow change.

### Run

Python 3.10 or later; **standard library only**, with arbitrary-precision integers
and `fractions.Fraction`. No SymPy, floating point, expression evaluation or
sampling is used in acceptance.

```sh
python3 -m unittest discover -s scripts -p 'test_symplectic_reference.py' -v
python3 scripts/demo_symplectic_reference.py
python3 scripts/demo_symplectic_reference.py --write-dir /tmp/vastitas-symplectic
python3 scripts/symplectic_reference.py \
  /tmp/vastitas-symplectic/good_U.request.json \
  /tmp/vastitas-symplectic/good_U.certificate.json
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/check_boundaries.py
```

- [Verifier](https://github.com/MGYamada/Vastitas/blob/main/scripts/symplectic_reference.py): exact polynomials, independent
  binding/alternation/exterior-derivative/inverse checks, strict JSON CLI.
- [Examples](https://github.com/MGYamada/Vastitas/blob/main/scripts/demo_symplectic_reference.py): named positive and negative
  cases; optional separate request and certificate files.
- [Regressions](https://github.com/MGYamada/Vastitas/blob/main/scripts/test_symplectic_reference.py): mathematical examples,
  identity/revision mutations, malformed evidence, and CLI exit codes.

Polynomial arithmetic is shared with the [SOS cover reference](analysis-and-effects.md#sos-reference)
through [rational_polynomial_reference.py](https://github.com/MGYamada/Vastitas/blob/main/scripts/rational_polynomial_reference.py).
Its explicit arity generalizes the arithmetic while preserving the four-variable
default API here. The symplectic matrix, domain and derivative-witness audits
still require four variables, including for zero polynomials; the JSON schema
and supported symplectic fragment are unchanged.
The metric-free plane consumer also retains its four-variable ambient ring
(restricted to its first two variables), even when a polynomial is zero.
Shared compatibility regressions live in
[test_rational_polynomial_reference.py](https://github.com/MGYamada/Vastitas/blob/main/scripts/test_rational_polynomial_reference.py).

CLI exit codes: `0` accepted **reference** input, `1` rejected reference claim,
`2` malformed/unsupported input or file/JSON error. The JSON report includes the
complete expected subject and separate check outcomes. `not_checked` is never
success. Rejecting an unsupported certificate does not prove its mathematical
claim false.

### Exact fragment and conventions

Let `x = (q1,p1,q2,p2)`, `P = Q[x0,x1,x2,x3]`, and `h = 1+q1`. Polynomials
have exact rational coefficients and nonnegative integral exponents. The
geometric interpretation is in **real** coordinates via `Q → R`, not a manifold
over `Q` and not Float64 execution. A context may explicitly permute these four
coordinate labels; every monomial, frame position, derivative and `h` then uses
that exact ordering. Changing the order requires a new certificate with all
coefficients reindexed; there is no implicit coordinate transport.

The only domains are the entire declared `R^4` object and its principal open
`D(h) = {x | h(x) != 0}`. `principal_open` carries the actual sparse polynomial;
the verifier compares it with the context's `1+q1`. The open is defined by this
predicate, not by a supplied assertion that `h` is nonzero everywhere. Polynomial
continuity makes it an open subset; proving this in Lean remains an obligation.

A candidate is a **full** 4-by-4 polynomial matrix `A`. Once alternation passes,

```math
\omega_x(u,v)=u^T A(x)v,
\qquad \omega=\sum_{i<j} A_{ij}\,dx_i\wedge dx_j.
```

There is no factor of two in the upper-triangle coefficients. The tangent frame
and its declared dual cotangent frame are coordinate frames, not arbitrary
frames with unverified changes of basis. If `ω♭(v)=ω(v,·)`, its covector-column
matrix is `A^T`; consequently the inverse of `ω♭` is `(A^{-1})^T`. The checker
tests `A^{-1}` and both matrix identities, so this sign convention does not
silently replace `ω(v,·)` by `ω(·,v)`.

Inverse witnesses have the **restricted** representation `B=N/h^k`, where `N`
is a polynomial matrix and `k` is a nonnegative integer. This represents a
fragment of `P[h^{-1}]`; it is not a rational-expression parser. All entries use
one common denominator. Rational constant factors are absorbed in `N`.
Two-forms themselves have polynomial coefficients; exterior differentiation of
general localized forms is not implemented.

### What is bound and what is trusted

`verify(expected, certificate)` takes an independently supplied expected subject.
The CLI reads it from a separate request file. It must not be derived from the
untrusted certificate's own `subject`. Equality compares the **entire** immutable
subject, including:

| Component | Bound data |
| --- | --- |
| Context | Environment snapshot, nominal geometric object and base, chart, ordered coordinates, tangent and dual cotangent frame identities |
| Interpretation | Fixed exact scalar profile, selected model identity and model revision |
| Domain | `all`, or `principal_open` with its complete generator polynomial |
| Form | Nominal form identity, revision, and every coefficient of the complete matrix |

Names, equal dimensions, determinants and sample values never replace this
equality. The polynomial normal form identifies equal rational polynomials,
without identifying distinct nominal contexts or forms. There is no digest-only
cache or externally supplied `verified` flag. Unknown JSON fields, duplicate
keys/monomials, floats, Boolean integer substitutes, negative exponents and
string expressions are rejected.

**Reference trust boundary:** context identities are synthetic nominal labels,
not authenticated compiler IDs or proof of model laws. Matching labels binds a
calculation to a request; it does not establish that those labels refer to a real
source object. The exact polynomial-to-real interpretation is fixed by this
experiment, not inferred from an arbitrary `model_id`. Rewriting both request
and certificate changes the statement being checked; production must derive
the request from the checked environment and actual Core. Python execution,
`Fraction`, JSON decoding and this implementation remain unproved. The API does
not defend against reflective mutation of Python objects or resource exhaustion
from enormous finite inputs; a production decoder needs independent limits.

### Separate checks and the nonzero boundary

1. **Binding:** require exact equality with the independent request. On failure,
   all mathematical checks are `not_checked`; evidence has the wrong subject.
2. **Alternation:** check every diagonal entry is zero and `A_ij + A_ji = 0`
   coefficientwise. An invertible non-alternating matrix cannot become a 2-form
   by discarding its lower triangle.
3. **Exterior derivative:** for each increasing triple compute

   ```math
   (d\omega)_{ijk}=\partial_i A_{jk}-\partial_j A_{ik}+\partial_k A_{ij}.
   ```

   Compare all four coefficients with the supplied derivative witness, then
   require all four to be zero. A wrong witness and an honest nonzero derivative
   receive distinct diagnostics. If alternation fails, this check is skipped
   because the full matrix does not denote the claimed 2-form.
4. **Domain-qualified inverse:** first justify the denominator, then check both
   `A*N = h^k I` and `N*A = h^k I` as polynomial identities. This check still runs
   when closedness fails, to expose their independence. Passing it alone never
   accepts a symplectic structure.

| Claim | What this fragment can check |
| --- | --- |
| Nonzero constant denominator | Encoded in rational coefficients; denominator integers must be positive |
| `h^k != 0` on `D(h)` | Follows from the structural membership condition and nonnegative integral power; no samples or string assumptions |
| `h^0 != 0` on all `R^4` | It is exactly `1`; polynomial inverse witnesses are allowed globally |
| `h^k != 0` on all `R^4`, `k>0` | Rejected **before clearing denominators**; `q1=-1` is outside the witness's validity |
| Global validity after cancellation of `h/h` | Not inferred. Supply a polynomial witness with `k=0`; removable-singularity proofs are outside this fragment |
| `1+q1^2 != 0`, arbitrary positivity/inequalities, other opens | Additional real-algebraic/domain evidence and a checked interpretation would be required; no proof hook currently accepts these claims |
| Cover inclusion, overlap agreement, coordinate changes or extension to a larger open | Additional restriction/transition/descent evidence required; not implemented |

For example, `(1+q1^2)dq1∧dp1 + dq2∧dp2` is globally closed and nondegenerate,
but its general rational inverse is outside this witness language. An unsupported
result is not a degeneracy theorem. Likewise a nonzero polynomial determinant
means "not identically zero", not "nonzero at every real point". Determinants
are computed only in regressions, never in acceptance.

### Positive and negative examples

For `f=(q1,p1,q2,h*p2)` and `ω0=dq1∧dp1+dq2∧dp2`, the tests reconstruct the
Jacobian and verify `A_good=J_f^T A0 J_f`, including the cross-term sign:

```math
\omega_{good}=dq_1\wedge dp_1+h\,dq_2\wedge dp_2-p_2\,dq_1\wedge dq_2,
\qquad
\omega_{bad}=dq_1\wedge dp_1+h\,dq_2\wedge dp_2.
```

Both have determinant `h^2` and the same matrix at the origin. Their derivatives
are respectively zero and `dq1∧dq2∧dp2`. The supplied good inverse is `N/h` with

```math
N=\begin{pmatrix}
0&-h&0&0\\
h&0&0&-p_2\\
0&0&0&-1\\
0&p_2&1&0
\end{pmatrix}.
```

| Demo case | Expected result |
| --- | --- |
| `good_U` | All checks pass on `D(h)` |
| `bad_U` | Alternation and inverse pass; `NOT_CLOSED` |
| `bad_forged_closedness` | `DERIVATIVE_WITNESS_MISMATCH` |
| `global_stale_evidence` | `SUBJECT_MISMATCH`: original U certificate cannot be used globally |
| `global_relabelled_evidence` | Rebinding the certificate does not fix the missing denominator proof: `DENOMINATOR_NOT_JUSTIFIED` |
| `same_determinant_replay` | `SUBJECT_MISMATCH`: equal determinant does not bind evidence |
| `same_determinant_relabelled` | The old derivative and inverse witnesses both fail after relabelling |

The tests additionally substitute `q1=-1` while leaving the other coordinates
symbolic: a 2-by-2 minor is `1` and **every** 3-by-3 minor vanishes for both
matrices. Thus rank is two throughout this hyperplane, not merely at a numeric
sample. Standard constant `ω0` is accepted on all `R^4`; the zero form fails the
inverse check. A non-alternating invertible matrix, a changed inverse entry,
changed object/base/frame/order/model/revision and malformed wire data are also
covered. These are finite executable regressions, not universal proofs.

### Lean soundness obligations (not proved here)

The following are proposed specifications, **not existing Lean declarations or
proofs**. Do not add `sorry`, axioms or an assumption named `Symplectic` to disguise
the missing argument. In a later implementation, put the executable checker in
the mathlib-free kernel and import its actual definitions into the proof-only
oracle. A copied abstract checker does not establish the implementation theorem.

| ID | Required statement and independent semantics |
| --- | --- |
| S1 | Decode canonical rational polynomials into `MvPolynomial (Fin 4) Q`; prove normalization, addition, multiplication, powers and equality checks preserve evaluation in `R`. Connect the Python reference to that executable representation by explicit refinement or classify it as a differential-test oracle only. |
| S2 | Interpret the nominal context as the same declared real coordinate object, base and coordinate/dual frames; interpret `all` and `D(h)` as sets. Prove `D(h)` is open and membership implies `h(x)^k != 0`. Never assume this on all `R^4` for `k>0`. |
| S3 | Prove alternation checking yields a continuous alternating bilinear form at each point with the stated coefficient and sign convention; polynomial coefficients are smooth. Do not define an arbitrary non-alternating matrix to be an alternating map by silently projecting it. |
| S4 | Prove symbolic partial derivatives equal real Fréchet derivatives; show the four computed triple coefficients represent the independent exterior derivative. Then a successful closedness check implies `dω=0` on the declared open. |
| S5 | From the actual successful denominator and two polynomial-product checks, derive for every `x` in the declared domain that `B(x)=N(x)/h(x)^k` is well defined and both inverse identities hold. Derive a fiberwise linear equivalence for `ω♭`, with its transpose convention and the same `x`; localized inverse coefficients are smooth on this open. |
| S6 | Prove the composite checker returns evidence indexed by the **exact expected subject** and only if S2–S5 hold for that subject. A changed field/polynomial must require equality transport or rechecking. No hash equality or determinant equality substitutes for subject equality. |

The independent exterior-derivative comparison is mathlib's
[`extDeriv` / `extDeriv_apply`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/DifferentialForm/Basic.html#extDeriv_apply).
Its alternating derivative convention gives the triple formula above. For the
pullback example,
[`extDeriv_pullback`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/DifferentialForm/Basic.html#extDeriv_pullback)
requires differentiability of the target form and sufficient `ContDiffAt`
regularity of the map (the theorem states a `minSmoothness R 2` bound). These must
be supplied from polynomial smoothness; the theorem is not an unconditional
rewrite. On an open domain, use the appropriate restriction/within theorem and
its domain/regularity hypotheses. This documentation was consulted on
2026-10-29; the future proof must use the repository's pinned mathlib API.

Concretely, with independently defined denotations, S6 should have this shape:

```text
checkReference expected certificate = ok result
  => result.subject = expected
     ∧ IsOpen (domain expected)
     ∧ SmoothTwoFormOn (denoteForm expected) (domain expected)
     ∧ ∀ x ∈ domain expected,
         extDeriv (denoteForm expected) x = 0
         ∧ (denoteForm expected x).flat is a linear equivalence
```

Here the form is a globally polynomial real-coordinate form restricted to the
open. The independent `SmoothTwoFormOn` predicate must include alternation; it
must not be defined as checker success. Failure need not imply the negation of
this predicate, because the certificate language is incomplete.

### Actual accepted-Core connection and architecture

The production dependency order remains **Lawvere first**:
[#204](https://github.com/MGYamada/Vastitas/issues/204) named theories/models,
operation interpretation, law evidence, ownership and structural orphan/dispatch
coherence; then the needed smooth form/bundle/domain semantics; then registration
of the composite symplectic profile. The synthetic model tags here neither
implement that prerequisite nor allow it to be skipped. Lawvere laws alone do
not establish analytic regularity, closedness or nondegeneracy.

The fixed **8 Domain Checkers + independent Ownership/Borrow** division remains:

| Existing jurisdiction | Obligation for this consumer |
| --- | --- |
| Graph | Typed wedge/contraction structure and approved structural operations |
| Fiber/Basepoint | Same manifold, point, tangent/cotangent fibers and frames |
| Linearity | Alternating bilinear form and domain-qualified inverse/equivalence |
| Regularity | Polynomial/localized smoothness and exterior-derivative correspondence/closedness |
| Descent | Restrictions, transitions, overlaps and covers if later introduced; this single global coordinate fragment supplies no gluing theorem |
| Base/Coefficient/Grading | Exact coefficient interpretation, real geometric base and form degree |
| Coherence | Unique explicitly selected named structural model and lawful operations |
| Provenance | Actual environment/owner/revision evidence and invalidation on changes |
| Independent Ownership/Borrow | Storage, aliasing, lifetimes and resource safety; polynomial symplectic acceptance proves none of these |

The future bridge under [#184](https://github.com/MGYamada/Vastitas/issues/184)
must extract its data from **one actual public acceptance result**. The current
[`Indexed.Wire.check`](https://github.com/MGYamada/Vastitas/blob/main/lean-kernel/VastitasKernel/IndexedAcceptance.lean)
records the exact decoded input and `AuthoritySource.checkProgram` result; it has
no symplectic consumer today. The finite edit theorem's exact-input/returned-Core
discipline is relevant, but its existing conclusion does not contain this
geometric contract. The following new obligations remain:

1. Obtain the expected subject from the accepted environment, nominal objects,
   selected model/operations, actual source occurrence and **actual returned
   Core**. Authenticate model laws/authority and dependency revisions; reject
   annotation-only `closed=true` or frontend-invented domain/identity data.
2. Prove extraction/interpretation correspondence: the actual Core denotes the
   specified form and its domain, including coefficient order, base, frame,
   pullback sign and selected interpretation. Merely finding another well-typed
   Core with a matching determinant is insufficient.
3. Connect the actual verifier success equation to S6, for that same subject,
   input, environment, policy, snapshot and returned Core. Preserve this binding
   through specialization and optimization, or explicitly recheck after changes.
4. Compose only the applicable domain obligations and independent Core Safety;
   do not fill missing domains with `Verified=True`. A native/FFI or numerical
   lowering additionally needs its own refinement and safety argument.

In proposed notation, not a new implemented API:

```text
ActualAccept(P,E,Q) = ok accepted
  => let C = accepted.returnedCore
     ∃ S evidence,
       ExtractSymplecticSubject(E,P,C,occurrence) = ok S
       ∧ CheckActualCertificate(E,S,evidence) = ok checked
       ∧ checked.subject = S
       ∧ DenoteActualCore(E,C,occurrence) = DenoteRequestedForm(S)
       ∧ SymplecticOn(DenoteRequestedForm(S), DenoteRequestedDomain(S))
       ∧ ApplicableDomainObligations(P,E,Q,C)
       ∧ IndependentCoreSafety(P,E,Q,C)
```

This implication is for a future acceptance route that **actually includes a
symplectic occurrence and the relevant checks**, not for every program or for
the current public acceptance function. Other occurrences must be separately
indexed. Certificates for a different Core, domain, environment revision or
unrelated named model cannot satisfy it by relabelling.

No general smoothness decision procedure, cover solver, Kähler construction,
complex integrability guarantee, new checker or production `std::geometry`
implementation is supplied here. The refined std/ecosystem boundary of #211 is
preserved; the historical ratified ADR is not silently rewritten.

<a id="variational-reference"></a>

## Exact polynomial first-variation reference

This is an **external Python reference** for the first boundary-term examples in
[#305](https://github.com/MGYamada/Vastitas/issues/305). It compares two finite
exact calculations and rejects malformed or mismatched evidence. It does not
implement `std::analysis::variational`, general function-space differentiation,
Lean soundness, or acceptance by Vastitas's actual source/checked-Core path.
The broader issue remains open.

### Supported mathematical profile

One real scalar path `q(t)` and one variation `eta(t)` on the positively oriented
interval `[0,1]`, both represented by `Q[t]`. A first-order Lagrangian is an
arbitrary finite rational polynomial `L(t,q,v)` with `v=q'`. The roles `t,q,v`
have an explicit ordered permutation in every Lagrangian; arity alone does not
establish variable identity. There are no rational-function denominators or
nonpolynomial operations. Rational coefficients have their usual real
interpretation; floats and bools cannot stand in for exact evidence scalars.

The action and its first variation for the supplied pair are

```text
S(q)             = integral_0^1 L(t, q(t), q'(t)) dt
delta S_q(eta)   = [epsilon^1] S(q + epsilon*eta).
```

For this finite polynomial perturbation, the action is a polynomial in epsilon.
Extracting its linear coefficient is an exact calculation, not a finite
difference or a sampled derivative. The result is the **scalar evaluation of a
linear functional at eta**, not a tangent vector or gradient. No metric, Riesz
identification, inner product or conjugation is selected.

The two supported variation spaces are unrestricted polynomial variations and
polynomial variations with `eta(0)=eta(1)=0`. A fixed-endpoint request checks
both values, with exact arithmetic, before either computation. The endpoints
of `q` need not be zero. Other constraints, support conditions and variation
spaces are not inferred. In particular, zero boundary contribution does not
prove fixed-endpoint admissibility: the two nonzero boundary values could
cancel, or the momentum could vanish.

### Arithmetic reuse and dependency status

[#281](https://github.com/MGYamada/Vastitas/pull/281) owns the introduction of the
[arity-aware shared Poly](https://github.com/MGYamada/Vastitas/blob/main/scripts/rational_polynomial_reference.py), the
symplectic extraction and the four-variable compatibility checks for both
symplectic and metric consumers, including zero polynomials. This increment
depends on that change and contains no second extraction or polynomial type.
It does not import the SOS producer/verifier. The shared compatibility tests
live in `test_rational_polynomial_reference.py` alongside the common arithmetic.

The integral-enclosure reference in
[#315](https://github.com/MGYamada/Vastitas/pull/315) also reuses #281. Its
univariate coefficient antiderivative, partition and local-error checks remain
independent of the variation and boundary-term checks here. The small shared
[polynomial calculus module](https://github.com/MGYamada/Vastitas/blob/main/scripts/rational_polynomial_calculus.py) adds
simultaneous substitution, exact evaluation and coefficientwise integration
using the same Poly. Integration removes the selected variable and preserves
the order of the remaining parameters. It uses the monomial rule
`c*(b^(n+1)-a^(n+1))/(n+1)`. Its arithmetic primitive supports rational endpoints;
the variational consumer deliberately accepts **only `[0,1]`**.

This is no integral-enclosure verifier, approximation/error-bound framework,
adaptive quadrature or additional AD engine. Differentiation uses the existing
`Poly.derivative` operation. Both computation routes share this arithmetic, so
their agreement is not independent verification of Python or the common
polynomial implementation. Primitive regressions separately test the
fundamental theorem on a finite polynomial family, parameter ordering, exact
small fractions and a polynomial with zero endpoint samples but nonzero integral.

### Two calculation routes

1. `direct_first_variation` substitutes `q+epsilon*eta` and
   `q'+epsilon*eta'` into the **whole** Lagrangian in `Q[t,epsilon]`, integrates
   out `t`, retains the full `Q[epsilon]` action, and extracts its linear
   coefficient. It never differentiates L or calls the bulk/boundary route.
2. `bulk_boundary_first_variation` independently computes the partials `L_q`
   and `L_v`, substitutes the actual path, and differentiates the substituted
   `L_v` in `t`. This retains explicit time dependence and acceleration terms.
   It returns the full polynomial coefficient and the separate contributions:

```text
p(t)       = L_v(t, q(t), q'(t))
EL(t)      = L_q(t, q(t), q'(t)) - d_t p(t)
bulk       = integral_0^1 EL(t) * eta(t) dt
boundary_0 = p(0) * eta(0)
boundary_1 = p(1) * eta(1)
boundary   = boundary_1 - boundary_0
delta      = bulk + boundary.
```

The boundary is **always computed**, even for fixed endpoints. Its value is
never replaced with zero on the strength of a tag. `EL` follows the stated
minus sign convention; for `L=(v^2-q^2)/2` it is `-q''-q`. The local equation
`EL=0`, the scalar first variation on a selected eta, and stationarity over
an entire admissible space are different statements. The API does not infer
stationarity from a zero coefficient or one zero first variation.

### Evidence and independent request binding

`propose` supplies the bulk/boundary decomposition and the variation endpoint
values. `verify(expected_subject, evidence)` first requires equality with an
**independently supplied** Subject, then recomputes admissibility, both routes,
and every supplied component. It compares the entire EL polynomial, bulk,
both oriented endpoint contributions, boundary difference and final total
separately. A compensating wrong bulk and boundary cannot pass by preserving
the sum. A mocked incorrect decomposition is also caught by the direct route.

The subject binds the named Lagrangian and defining revision, actual
coefficients, variable order, path and variation coefficients, exact interval,
admissible variation space, environment, configuration identity, scalar profile
and reference ruleset. Equal numerical answers do not erase these distinctions.
Changing the Lagrangian by a constant or swapping symmetric variable roles
still invalidates old evidence. Different intervals are rejected both as stale
subjects and, after relabelling, as unsupported profiles.

Changing both the expected subject and the evidence label is not a shortcut:
all content is recomputed. Correct freshly recomputed evidence for another
supported subject can of course pass. IDs/revisions here are **fixture data**,
not authenticated proof declarations. Frozen Python dataclasses do not confer
authority; consumers must call `verify` again rather than trust a constructed
`Evidence` or `ReferenceCheck`. The returned result retains the exact expected
subject and freshly computed values.

### Reproduction and regressions

Only Python's standard library is needed. From the repository root:

```sh
python3 -S scripts/demo_variational_reference.py
python3 -m unittest discover -s scripts -p 'test_variational_reference.py' -v
python3 -m unittest discover -s scripts -p 'test_rational_polynomial_calculus.py' -v
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/check_boundaries.py
git diff --check
```

The demo emits exact rational strings in JSON. Existing CI discovers the new
tests through its current `test_*.py` pattern.

| L; q; eta | EL along q | Direct first variation | Bulk | Boundary |
| --- | --- | --- | --- | --- |
| `q*v`; `t`; `t` | `0` | `1` | `0` | `1` |
| `q*v`; `t`; `t*(1-t)` | `0` | `0` | `0` | `0` |
| `(v^2-q^2)/2`; `t`; `t*(1-t)` | `-t` | `-1/12` | `-1/12` | `0` |
| `q*v`; `t+2`; `1` | `0` | `1` | `0` | `3-2` |
| `t*v`; `t`; `t*(1-t)` | `-1` | `-1/6` | `-1/6` | `0` |
| `v^2/2`; `t^2`; `t*(1-t)` | `-2` | `-1/3` | `-1/3` | `0` |

The tests also include 80 nonlinear Lagrangian/path/variation combinations,
all six correctly reindexed variable orders, a finite family of total
derivatives, rational linearity in eta, constant/linear Lagrangians, the full
epsilon action, and a nonzero boundary as small as `10^-30`.

Negative cases cover omitted/reversed boundaries, wrong lower-endpoint signs,
swapped endpoint values, wrong EL signs, forged totals and compensating errors,
forged fixed-endpoint tags/traces, inadmissible variations with zero boundary,
and stale Lagrangian identity/revision/body, interval, variable order, variation
space, path, eta, environment or configuration. A relabelled variation with the
same endpoint traces still has its interior contribution recomputed.

### Remaining obligations

| Layer | Status and obligation |
| --- | --- |
| Finite Python reference | Exact coefficient/endpoint calculations and instance equality for tested inputs, plus mutation rejections. This is executable evidence, not a universal formal proof. |
| Polynomial mathematical semantics | Prove soundness of substitution, partial/total differentiation and integration over the real interpretation; prove coefficient extraction gives the derivative of the finite polynomial action and the bulk-plus-boundary identity with its sign. |
| General function spaces | Separately select configuration/test-function spaces, topology, regularity, integrability, continuity/linearity of the derivative, boundary traces and justified differentiation under the integral/integration by parts. No extension from finite tests is automatic. |
| Lean soundness | Formalize the actual supported implementation and prove acceptance implies the independently defined first-variation statement and the actual endpoint premises. Under #285, separate mathematical definitions, implementation soundness and pinned-mathlib correspondence. No new axioms or proof completion are supplied here. |
| Actual accepted Core | Resolve/authenticate definitions, revisions, ordered roles, domain and admissible spaces from the real environment; bind the verified result to the exact returned Core; reject forged, stale and swapped evidence through real source/IR acceptance. No source or Core variational feature currently follows from this reference. |
| Native realization | Any later backend needs a separate refinement/rounding contract. Exact Python arithmetic says nothing about native numerical error or performance. |

No ODE/PDE solving, general jet-bundle construction, Noether theorem, constrained
stationarity solver, higher-order/vector/multidimensional action, infinite
domain, integral enclosure or alternative differentiation engine is added. The
existing 8 Domain Checkers plus Ownership/Borrow Checker and CS/MS/CF remain the
architectural framework; this reference creates no additional checker or
constitutional theorem.

<a id="cech-reference"></a>

## Finite open-cover Čech reference (#265)

This is a **Python reference calculation and regression suite**, not a Vastitas
language feature, a Lean proof, or production acceptance. It implements only a
small finite-open fragment of [#265](https://github.com/MGYamada/Vastitas/issues/265).
The general complex/homology contract remains with
[#258](https://github.com/MGYamada/Vastitas/issues/258). No general sites,
characteristic classes, spectral sequences, resolutions, or second homological
algebra library are implemented.

Baseline: main `d783b5a6e393214a54cb408501963b1e42a7be94`.
Python 3.10+, standard library only, with arbitrary-precision integers:

```sh
python3 -m unittest discover -s scripts -p 'test_cech_reference.py' -v
python3 scripts/demo_cech_reference.py
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/check_boundaries.py
```

- [Reference](https://github.com/MGYamada/Vastitas/blob/main/scripts/cech_reference.py): finite topology, intersections,
  componentwise sections, restrictions, alternating differential and binding checks.
- [Demo](https://github.com/MGYamada/Vastitas/blob/main/scripts/demo_cech_reference.py): JSON containing separate check
  outcomes, proposed complex input, cover provenance and exact integer witnesses.
- [Tests](https://github.com/MGYamada/Vastitas/blob/main/scripts/test_cech_reference.py): 28 regression cases, automatically
  discovered by the existing Python CI step. No workflow change is needed.

Validation: all 28 focused tests passed; full Python discovery ran 237 tests
with 236 passes and one existing live compiler integration skip (the Rust CLI
and Lean kernel binaries are not built in this environment). The dependency
boundary checker passed. No Rust or Lean source changed; no new compiler or
Lean build result is claimed.

### Fixed semantic profile and independent checks

The input is a nonempty space of at most eight explicitly named points, its
complete finite topology, and one to four **ordered, labelled** cover members.
The checker verifies that the topology contains the empty set and whole space,
contains only point subsets, and is closed under pairwise unions/intersections.
Since the family is finite, these conditions give finite intersections and
arbitrary unions. It separately verifies that every cover member is open and
their union is the whole space. Duplicate cover *opens* are allowed under
distinct labels; empty members are allowed. These are reference size limits,
not mathematical restrictions on #265.

For each nonempty increasing index tuple, the checker recomputes the actual
intersection from the cover sets. It retains **empty intersections explicitly**.
It never uses the submitted intersection table to compute the expected complex.
The current convention is the increasing-index alternating Čech complex;
changing ordering/bases requires reconstruction or future proved transport.

The coefficient object is the **locally constant integer sheaf**: sections on
an open U are integer-valued locally constant functions, represented by one Z
per connected component. This is not the constant presheaf assigning one Z to
every nonempty open. In a finite space, components are obtained from the
undirected specialization graph, using minimal open neighbourhoods computed
from the topology. In particular F(empty)=0, while a disconnected open can
have multiple generators. The future equivalence with the sheaf interpretation
is an explicit proof obligation below.

For V contained in U, every component of V lies in one component of U. The
restriction matrix has one row per V-component and one column per U-component,
with entry 1 precisely for that containment. We retain all inclusions among
the actual intersection opens, including identities and maps to the empty set.
Thus both the **actual restriction functions** and their **identity/composition
laws** can be checked separately. A different functor with zero maps on proper
inclusions can satisfy the laws while failing to represent the chosen sheaf.

For an increasing tuple J=(j_0,...,j_(p+1)), the component of the differential is

```math
(dc)_J=\sum_{k=0}^{p+1}(-1)^k
 \operatorname{res}_{U_{J\setminus j_k},U_J}(c_{J\setminus j_k}).
```

All matrices act on column vectors. The checker compares the submitted maps
with this alternating construction and separately multiplies adjacent submitted
differentials over Z. Matrix dimensions remain explicit even for zero rows or
columns. There is no floating-point tolerance or rational-rank acceptance.

| Check | What is checked independently |
| --- | --- |
| Binding/profile | Exact expected subject and supported finite-open / locally constant Z profile |
| Topology / cover | Actual topology axioms / actual open-cover condition |
| Overlaps | Complete increasing tuple table equals recomputed intersections |
| Sections | Ordered section bases equal components of those actual intersections |
| Restrictions | Complete typed restriction diagram equals restriction of locally constant functions |
| Restriction laws | Identities and every composable inclusion triangle |
| Orientation | Returned complex equals the fixed alternating construction, including coefficient identity and ranks |
| Endpoints | Internal ranks, differential count and source/target matrix dimensions |
| d squared | Each adjacent matrix product is exactly zero |

Malformed immutable records are rejected with `Invalid`. A changed subject
blocks subsequent checks; unsupported site/coefficient profiles are reported
as `unsupported`. Missing or ill-typed maps produce `not_checked` for the
dependent laws/product. Neither status counts as success. Well-typed candidate
matrices can still have their d squared checked when their geometric checks
fail; that result is algebraic only. All checks must pass before `returned`
contains a candidate. `propose` is a convenience producer, not an authority.

### Six-point model and the adversarial complex

The points are v0,v1,v2,e01,e02,e12, ordered by face inclusion. Opens are upper
sets. Exhaustive enumeration gives 18 opens, with the cover

```text
U0 = {v0,e01,e02}
U1 = {v1,e01,e12}
U2 = {v2,e02,e12}
```

The pair intersections in order 01,02,12 are {e01},{e02},{e12}; the triple
intersection is empty. Each nonempty intersection is connected. Hence

```math
C^0=\mathbb Z^3,\quad C^1=\mathbb Z^3,\quad C^2=0,\qquad
D=d^0=\begin{pmatrix}-1&1&0\\-1&0&1\\0&-1&1\end{pmatrix}.
```

All degrees beyond the finite presentation are zero. This statement concerns
**this Čech complex only**, not derived-functor sheaf cohomology.

| Candidate | Geometric / orientation result | d squared | H1 of candidate complex |
| --- | --- | --- | --- |
| Actual cover | All checks pass | Zero | Z |
| Invented triple intersection, C2=Z, d1=(1,-1,1) | Overlap, section basis and orientation fail | Zero | 0 |
| One incorrect sign in original d0 | Orientation fails | Zero because C2=0 | Not used for acceptance |
| Three genuine identical opens of a point, then wrong d1=(1,1,1) | Overlaps pass; orientation fails | Nonzero | Not computed |
| Reuse on another cover, coefficient or site | Binding fails | Not checked | Not borrowed |

For the fake complex, the added point {e01} is not even contained in the other
two pair intersections. Matrix algebra cannot repair that missing geometric
origin. Conversely, on the one-point space a genuine three-member repeated
cover has exactly the matrices D and (1,-1,1) and is accepted. Identical matrices
do not determine which space/site/cover they represent.

### Integral kernel, image and quotient witnesses

The executable witness routine is deliberately restricted to the two displayed
triangle presentations. It is not a general Smith normal form or homology
implementation. It verifies the following **integer** matrices and their
explicit integer inverses:

```math
U=\begin{pmatrix}1&0&0\\0&1&0\\1&-1&1\end{pmatrix},\quad
V=\begin{pmatrix}0&0&1\\1&0&1\\0&1&1\end{pmatrix},\quad
UDV=\operatorname{diag}(1,1,0).
```

Both products U U_inverse and U_inverse U, and likewise for V, are checked
against the identity. Thus this is a unimodular change of integral bases.
The kernel of D is Z(1,1,1), and its image has basis
b1=(1,0,-1), b2=(0,1,1).

Let q(a,b,c)=a-b+c, g(n)=(0,0,n), and S(a,b,c)=(0,a,b). The program checks
the full matrix identities

```math
qD=0,\qquad qg=1,\qquad DS+gq=I_3.
```

In particular, every integral y=(a,b,c) decomposes as

```math
y=D(0,a,b)+(a-b+c)(0,0,1).
```

Consequently im(D)=ker(q), q is onto Z with integral section g, and
Z^3/im(D) is Z, with no torsion. For the actual complex ker(d1)=Z^3, so
H0=Z and H1=Z. For the fake complex d1=q, hence ker(d1)=im(D) and H1=0.
In the JSON, `cokernel_d0_map` and its section describe the ambient cokernel
C1/im(D) in both cases; they are not a section of the fake complex's H1.
This gives kernel, image and quotient arguments without inferring an integral
answer from dimensions over Q. The tests also double D: the same U,V yield
diag(2,2,0), and b1 cannot lie in im(2D) because its first coordinate is odd.
The original integral witness is rejected despite unchanged rational rank.

These are executable exact identities plus the stated elementary argument;
they are not yet Lean-checked proofs.

### #258 handoff versus #265 provenance

`ComplexData` is a **proposed data boundary**, not an existing std::category::abel
API: it contains the selected integral coefficient identity, finite graded
ranks and exact differential matrices. It uses local integer basis slots and
implicitly zero terms outside the finite range. General kernels, images,
quotients, homology functoriality and derived-functor machinery belong to #258;
this reference implements none of those generically.

`CoverData` is the #265 sidecar: actual intersections indexed by the ordered
cover, bases labelled by intersection/component, and actual restriction maps.
`Candidate.subject` binds both to the complete topology and cover plus the
environment, space, site, coefficient, sheaf, cover and model-revision identities.
Consumers must carry the sidecar/subject when claiming that a #258 complex is
cover-derived. Passing only matrices loses that claim.

`verify(expected, candidate)` takes the expected subject independently and
compares complete immutable values, not hashes, matrix equality alone or
caller-supplied success flags. Changed identities require fresh checking even
when the mathematics looks identical. Retagging the entire candidate still
causes reconstruction; changing both inputs cannot import external authority.
Python records and these synthetic identifiers do not authenticate ownership,
dependencies or a real compiler environment. A consumer must replay verification
against its current expected subject, not treat a constructed `Report` as proof.

### Additional evidence and future proof obligations

No result here certifies overlap acyclicity, higher **sheaf** cohomology
vanishing, an acyclic/good cover, or comparison with a circle, singular
cohomology or derived global sections. Even the one-member cover {X} of this
six-point space passes finite-cover checking and has zero positive-degree
Čech terms. The checker does not infer a sheaf-cohomology vanishing theorem
from that truncated complex.

For a Čech-to-sheaf comparison, first supply the abelian sheaf/category and
derived-global-sections framework with its admissible resolution hypotheses,
then an actual comparison map and theorem with applicable hypotheses. One
possible route requires acyclicity of the chosen sheaf on every relevant
nonempty finite overlap: all positive-degree derived groups there vanish.
Finiteness, connectedness, d squared zero and computed matrix ranks do not
provide those premises. Any circle/singular comparison would separately need
an interpreted finite model and an appropriate proved comparison. Neither is
implemented here, and there is no comparison-evidence acceptance API.

The future Lean work must establish, against independent mathematical semantics:

1. Finite topology/cover acceptance implies the actual open-cover predicate;
   every returned intersection is its set-theoretic intersection.
2. The component representation denotes locally constant Z-valued sections
   (including empty and disconnected opens), with a lawful abelian sheaf
   interpretation. Returned matrices denote the actual restrictions and satisfy
   their identities/composition, not merely an arbitrary lawful presheaf.
3. The chosen ordered bases and alternating signs denote the Čech differential;
   face cancellation proves d squared zero. Executable integer matrix operations
   agree with the abelian-group maps supplied to #258.
4. Acceptance returns exactly those complex/provenance data for the same subject.
   Prove the fixed integer splitting identities and their kernel/image/quotient
   interpretation using #258, rather than introducing another homology library.

Implement executable checks in the **mathlib-free `lean-kernel/`**, with proofs
in `lean/` importing that actual implementation. No `sorry`, custom axiom,
second Boolean checker, or Python success flag can discharge these obligations.
Failure of this bounded reference is not a universal nonexistence theorem.

For the accepted-Core bridge, resolve the actual space/topology, cover, sheaf,
coefficients, selected operations and dependencies from the validated environment
and the exact protocol-7 executable Core. Bind the resulting subject to
`accepted.checked.executable.core.module`, prove the denotation of each extracted
section/restriction/differential agrees with that Core, and retain the exact
returned module in the evidence attachment consumed by codegen. The existing
[`IndexedWire.codegen_input`](https://github.com/MGYamada/Vastitas/blob/main/lean/VastitasOracle/IndexedWire.lean) equates
that module with the lowered module; it supplies no Čech theorem. Changes to
source, environment, coefficients, site, cover, ordering or selected method
must invalidate evidence or use proved transport for the actual transformed
Core. Compose these obligations through #184/#192 and existing checker
jurisdictions with independent Ownership/Borrow; do not add another top-level
Domain Checker. Storage/native refinement remains a separate obligation.

| Layer | Status of this increment |
| --- | --- |
| Finite topology/cover, sections/restrictions and integer matrices | Implemented and regression-tested Python reference |
| Kernel/image/quotient for the two fixed complexes | Explicit integral identities checked; argument above |
| General homological algebra | Remains #258's responsibility; not implemented here |
| Lean soundness and actual accepted-Core connection | Obligations only; no new Lean build/proof claimed |
| Acyclicity, sheaf/singular/circle comparisons | Require additional evidence/theorems; not certified |
| General sites, characteristic classes, spectral sequences | Outside this increment |

Ordinary compilation and generated programs do not import Python or this
reference. Rust, Lean kernel/oracle, public protocols and stdlib are unchanged.

<a id="ssh-toric-reference"></a>

## Exact SSH Bloch/Fermi reference

This is the first finite physics reference for
[#247](https://github.com/MGYamada/Vastitas/issues/247). It implements exact
external Python calculations and regression tests. It does **not** implement
`std::geometry::toric`, accept `.vast` programs, or establish a Lean theorem.
The general toric design and its acceptance checklist remain open.

### Run

From the repository root, with Python 3.10 or later and only its standard library:

```sh
python3 scripts/demo_ssh_toric_reference.py
python3 -m unittest discover -s scripts -p 'test_ssh_toric_reference.py' -v
python3 -m unittest discover -s scripts -p 'test_*.py'
```

The demo emits JSON containing exact equations, quotient multiplication matrices,
the three counterexamples, and named checks; it exits nonzero if a check fails.
Its status is explicitly `external_exact_reference_only`. The existing Python
CI discovery includes the new tests without adding SymPy or a compiler dependency.

Files: [arithmetic and presentations](https://github.com/MGYamada/Vastitas/blob/main/scripts/ssh_toric_reference.py),
[demo](https://github.com/MGYamada/Vastitas/blob/main/scripts/demo_ssh_toric_reference.py), and
[regressions](https://github.com/MGYamada/Vastitas/blob/main/scripts/test_ssh_toric_reference.py).

### Supported fragment and stored data

The arithmetic is finite sparse `QQ[v,w,E,z,z^-1]`, using `Fraction` coefficients
and exponent tuples in that fixed order. Only the exponent of `z` may be
negative. Normalization merges equal monomials and removes zero coefficients;
it never takes a radical or extracts a root set. Floats, Boolean coefficients,
negative parameter/energy powers and arbitrary rational-function inverses are
rejected. There is no expression parser or untrusted JSON input interface.

`TorusPresentation(coordinates, equation)` retains the affine presentation
`Spec(QQ[coordinates,z^-1]/(equation))`. The coefficient field is always `QQ`,
the inverted coordinate is always `z`, and remaining `v,w` are base parameters;
remaining `E` is the energy coordinate. `Specialization` retains its source,
target and exact assignments, and reconstructs the target equation to reject
inconsistent maps. Its scheme morphism is contravariant to this ring map.
Equal presentations are compared structurally; this is not a test of nominal
scheme identity or a decision procedure for isomorphism of presentations.

| Scheme data to preserve | This reference | Production obligation |
| --- | --- | --- |
| Base and ambient | `QQ`, remaining coordinates, and localization at `z` | Checked base/model identities and coordinate/group-ring interpretation |
| Defining ideal | One complete Laurent generator, including repeated factors | Quotient algebra and certified ideal comparisons, never automatic reduction |
| Family and fiber maps | Source, target, exact rational assignments; `E=0` is explicit | Base-change/fiber construction and endpoint correspondence |
| Multiplicity | The full double-point algebra with basis `1,epsilon` | Prove the quotient equivalence and module length over the stated residue field |
| Localized units | Signed `z` exponents and explicit inverse in the double point | Unit witnesses and localization universal property |
| Polynomial representatives | Clearing power, original generator, saturation witness | Extension/contraction certificate for the chosen affine/toric ambient |
| Spectral module/action | The actual SSH matrix remains separate from its determinant | Retain matrix/module data when kernel or Jordan information is required |
| Provenance | Fixed example and explicit presentation maps | Actual source/Core occurrence, nominal objects, owners, model laws, revisions and evidence binding |

All Python objects and operations are external reference representations, not
authenticated compiler evidence. The code does not implement general schemes,
quotients with arbitrary ideals, multivariate Laurent lattices, general matrices,
fan gluing, compactification, numerical bands or the physical unitary slice.
The algebraic torus is not restricted by `|z|=1`.

### Parameter family, fiber and specialization order

Over `R=QQ[v,w]`, the code constructs

```math
H=\begin{pmatrix}0&v+wz^{-1}\\v+wz&0\end{pmatrix},\qquad
P=\det(EI-H)=E^2-v^2-w^2-vw(z+z^{-1}).
```

The Bloch presentation is `Spec(R[z,z^-1,E]/(P))`, with its projection to the
parameter base and to the energy line over that base. The zero-energy Fermi
presentation is its fiber along `R[E] -> R`, `E -> 0`. Parameter specialization
uses `R -> QQ`, leaving `z` invertible. Tests compare these operations in both
orders and together, and compare specialization before/after the matrix
determinant. Exact independent scalar evaluations cover rational and negative
parameters as well as zero hoppings. No operation divides by `v` or `w`.

The symbolic coefficient test records that `P` is monic of degree two in `E`.
The corresponding future theorem is that the Bloch projection to the torus is
finite locally free of rank two, with basis `1,E`, including degenerate bands.
This is a different projection from the Fermi fiber over a fixed energy: that
fiber need not always have length two. At `v=w=0,E=0` its equation is zero
(the whole torus); at `(v,w)=(0,1)` or `(1,0),E=0` its equation is `-1`
(the empty scheme). The double-point adapter rejects these cases.

Polynomial representatives require care. Clearing the parameter-family
denominator first and then setting `v=w=0` gives `z*E^2`; specializing in the
Laurent ring first and then clearing minimally gives `E^2`. They differ as
polynomials but generate the same Laurent ideal. The code checks the equality
after restoring the recorded powers of `z`. Scheme-theoretic closure/saturation
must not be assumed to commute with arbitrary base change.

### The nonreduced zero-energy fiber

At `v=w=1,E=0`,

```math
P_0=-(z+1)^2/z,\qquad
A=\mathbb Q[z,z^{-1}]/((z+1)^2)
  \simeq\mathbb Q[\epsilon]/(\epsilon^2).
```

The exact adapter first checks the full specialized presentation, not its roots.
The factor `-z^-1` is a unit. The maps are `z -> -1+epsilon`,
`z^-1 -> -1-epsilon`, and conversely `epsilon -> z+1`. The relations show the
maps are mutually inverse; `1,epsilon` is a basis over `QQ`. Hence this is a
length-two point supported at the rational point `z=-1`.

`Dual(a,b)` retains both coefficients. Multiplication and inversion are

```math
(a+b\epsilon)(c+d\epsilon)=ac+(ad+bc)\epsilon,\qquad
(a+b\epsilon)^{-1}=a^{-1}-ba^{-2}\epsilon\quad(a\ne0).
```

Columns of the regular multiplication matrix are images of the ordered basis
`(1,epsilon)`:

```math
M_\epsilon=\begin{pmatrix}0&0\\1&0\end{pmatrix},\quad
M_z=\begin{pmatrix}-1&0\\1&-1\end{pmatrix},\quad
M_{z^{-1}}=\begin{pmatrix}-1&0\\-1&-1\end{pmatrix}.
```

Tests explicitly check `epsilon != 0`, `epsilon^2=0`, both inverse products,
and that the fiber equation vanishes in this algebra. Negative powers are also
compared with the independent first-order remainder
`z^n = (-1)^n + n*(-1)^(n-1)*epsilon` for integers `-9 <= n <= 9`.
The first column of multiplication by `a+b*epsilon` recovers `(a,b)`, so these
matrices retain the element, not just its eigenvalues.

The reduction map `a+b*epsilon -> a` kills a nonzero element and reduces the
vector-space dimension from two to one. Equations `z+1` and `(z+1)^2` have
the same point support, but `z+1` is nonzero in `A`. Replacing the SSH equation
by the reduced equation or a triple power fails the exact presentation check.
The SSH matrix itself has off-diagonal entries `-epsilon,epsilon` over `A`,
while its value at the reduced point is the zero matrix.

### Boundary component and restricted saturation

After `v=w=1`, minimal clearing gives

```math
F=zE^2-(z+1)^2=zP.
```

An extra clearing gives `zF`. In affine `Spec(QQ[E,z])`, `zF` vanishes on
the entire line `z=0`, while `F|_{z=0}=-1`. On the torus they differ by a unit;
their affine zero schemes differ. `polynomial_boundary_at_z_zero` is explicitly
evaluation in the polynomial ambient. Laurent specialization at `z=0` is
rejected even for a constant expression, because it is not a ring map from
the declared Laurent ring.

`saturate_principal_z` supports **one nonzero polynomial `f` in `QQ[E,z]`**.
It finds the smallest `z` exponent `k` in the support and returns `g=z^-k f`.
The independent witness checks require the exact original input, `k>=0`,
`f=z^k g`, and `g|_{z=0} != 0` as a polynomial. Here the last condition means
`z` does not divide `g`; it does not assert pointwise nonvanishing for all `E`.
In this UFD, with prime `z`, these facts give

```math
(f):z^\infty=(g).
```

For `f=zF`, the returned generator is `F`. Equivalently, the contraction after
adjoining `t` and `1-tz` recovers `(F)`; one inclusion has the elementary witness
`F=t(zF)+(1-tz)F`. The implementation does not run a general elimination engine.
It removes only the `z` factor: saturation of `z^k(z+1)^2` still returns
`(z+1)^2`. Wrong powers, altered generators, replayed original inputs and
radicalized answers fail the witness check.

This is not general ideal membership, ideal equality or saturation over arbitrary
rings. Lists of generators, remaining parameters `v,w`, Laurent input and the
zero polynomial are explicitly unsupported by this helper. The last restriction
is an API limit, not a claim that saturation of the zero ideal is undefined.
Arbitrary toric closures and general boundary certificates remain future work.

### Characteristic multiplicity is not Jordan structure

At the reduced point `v=w=1,z=-1`, the SSH matrix is zero. Compare it to
`J=[[0,1],[0,0]]`. Both characteristic polynomials are `E^2`, but exact scalar
kernel dimensions are respectively two and one. `J` is nonzero and `J^2=0`.
The zero matrix has minimal polynomial `E`; `J` has minimal polynomial `E^2`.
Thus no similarity or exceptional-point claim follows from equal characteristic
polynomials or their repeated factors. `kernel_dimension2` only handles exact
scalar 2-by-2 matrices and rejects unresolved parameters; it is not a Jordan
classification algorithm over a nonreduced algebra.

### Future stdlib and Lean obligations

These are specifications, not completed Lean declarations or `.vast` fixtures.

1. Define the admitted exact coefficient and group-ring models; prove sparse
   normalization and operations denote finite Laurent polynomials. Establish
   localization, units and the supported ring maps, preserving declared bases.
2. Prove the determinant interpretation and its naturality under coefficient
   base change. Construct the actual quotient/fiber and comparison isomorphisms;
   prove monicity gives a finite locally free Bloch projection of rank two.
3. Prove the specific double-point quotient equivalence, basis independence,
   nonzero nilpotent and unit formulas. Preserve the nonreduced structure through
   serialization and lowering; a point set or square-free equation is insufficient.
4. Prove the actual restricted saturation verifier implies the stated
   extension/contraction result under its `QQ[E,z]`/principal hypotheses.
   New coefficient rings or ideals need separately justified algorithms and
   certificates. Prove polynomial-boundary evaluation is distinct from the
   Laurent ring map; do not infer closure/base-change commutation.
5. Keep spectral action/module data when claiming kernel/Jordan properties.
   Equal characteristic polynomials alone cannot supply that evidence.
6. Bind all evidence to the same checked environment, source occurrence,
   coefficient/model identities, ambient, ideal, specialization maps and actual
   returned Core. Independently reconstruct/recheck these in the kernel and
   import those actual definitions into the proof-only oracle; tests of this
   Python model are not a proof about a separately implemented compiler.

Use the existing checker responsibilities and independent Ownership/Borrow
boundary; this reference introduces no Toric/Bloch Checker. A future backend
also needs operational refinement and resource safety. Python, `Fraction` and
this code remain trusted for these external calculations; no general resource
bounds or protection against reflective Python mutation are provided. Unsupported
operations and deferred obligations are never reported as mathematical acceptance.

<a id="elliptic-reference"></a>

## Exact elliptic addition reference (#253)

This is an executable **Python reference and regression suite**, scoped to
`E: y^2 = x^3 - x` over **F5**, and the explicitly listed rational boundary points
`O, (-1,0), (0,0), (1,0)` over **QQ**. It does not enumerate or classify all of
`E(QQ)`. It supplies no public `.vast` API, accepted Core, named `Group` instance,
Lean theorem, or group-scheme implementation.

The reference follows [#253](https://github.com/MGYamada/Vastitas/issues/253)'s
separation between point membership and correct group operations. The issue
also lists a different F5 curve, `y^2=x^3+x+1`, and broader acceptance cases;
those are not implemented here and the issue remains open.

### Run and reproduce

Python's standard library is sufficient; no CAS, float arithmetic or third-party
dependencies are used.

```sh
python3 scripts/demo_elliptic_reference.py
python3 scripts/demo_elliptic_reference.py --json
python3 -m unittest discover -s scripts -p 'test_elliptic_reference.py' -v
python3 -m unittest discover -s scripts -p 'test_*.py'
```

| File | Responsibility |
| --- | --- |
| [elliptic_reference.py](https://github.com/MGYamada/Vastitas/blob/main/scripts/elliptic_reference.py) | Fixed fields and curve, nominal handles, exact points, guarded addition, evidence replay, exhaustive finite group audit |
| [demo_elliptic_reference.py](https://github.com/MGYamada/Vastitas/blob/main/scripts/demo_elliptic_reference.py) | Human-readable table/JSON report and two deliberately invalid slope mutations |
| [test_elliptic_reference.py](https://github.com/MGYamada/Vastitas/blob/main/scripts/test_elliptic_reference.py) | Independent group-table oracle, projective enumeration, exception/identity/evidence regressions |
| [f5-y2-x3-minus-x.json](https://github.com/MGYamada/Vastitas/blob/main/tests/fixtures/elliptic/f5-y2-x3-minus-x.json) | Complete ordered 8-by-8 addition table, law counts, mutation witnesses, rational boundary results |

The regression compares the generated JSON with that committed record. Existing
CI already discovers `scripts/test_*.py`; no compiler dependency is introduced.

### Total inversion and formula applicability

The project's [mathlib lock](https://github.com/MGYamada/Vastitas/blob/main/lean/lake-manifest.json) pins revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`. Its
[field definitions](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/Field/Defs.lean)
include `DivisionRing.inv_zero`. The reference preserves `inv0(0)=0` in both
fields. F5 uses canonical integers in `0..4`; QQ uses `fractions.Fraction`.
Point construction accepts exact integers (and fractions for QQ), then stores
canonical values. Float and Boolean coordinates, and noncanonical raw claims,
are rejected.

`slope_inverse` checks that the denominator is nonzero **before** invoking total
inversion. This is a precondition on using the affine slope formulas, not a
partial definition of field inversion. Addition records the following branches:

| Branch | Condition | Result / applicability |
| --- | --- | --- |
| `left_identity` | Left point is O | Return right point, after validating both subjects |
| `right_identity` | Right point is O | Return left point, after validating both subjects |
| `double_y_zero` | Same affine point and y=0 | O; no inversion evaluated |
| `inverse_pair` | Same x and opposite y, after the previous case | O; no inversion evaluated |
| `tangent` | Same affine point and y nonzero | Slope `(3*x^2-1)/(2*y)`, with checked `2*y != 0` |
| `chord` | Remaining pair | Slope `(y2-y1)/(x2-x1)`, with checked `x2-x1 != 0` |

For the last two branches, `x3=lambda^2-x1-x2` and
`y3=lambda*(x1-x3)-y1`; the result is checked for exact membership again.
Distinct on-curve points with equal x in these two fields are inverse pairs,
so all admitted pairs reach a valid branch. The exceptional branches explicitly
precede any affine division.

O is represented by a tagged `None` coordinate, denoting `[0:1:0]` on
`Y^2 Z = X^3 - X Z^2`. It is not an unindexed global point and is never confused
with the affine point `(0,0)`. The tests independently enumerate homogeneous
triples over F5: 32 nonzero representatives modulo the four nonzero scalars
give precisely the eight points, with exactly one point at infinity.

The fixed discriminant is `-16*(4*(-1)^3)=64`, hence 4 over F5. It is attached
to the selected short presentation and exact field. The reference supports no
coefficient parameter, general Weierstrass model, or coordinate change.

### Full F5 table and independent expected values

| + | O | (0,0) | (1,0) | (2,1) | (2,4) | (3,2) | (3,3) | (4,0) |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| O | O | (0,0) | (1,0) | (2,1) | (2,4) | (3,2) | (3,3) | (4,0) |
| (0,0) | (0,0) | O | (4,0) | (2,4) | (2,1) | (3,3) | (3,2) | (1,0) |
| (1,0) | (1,0) | (4,0) | O | (3,3) | (3,2) | (2,4) | (2,1) | (0,0) |
| (2,1) | (2,1) | (2,4) | (3,3) | (0,0) | O | (1,0) | (4,0) | (3,2) |
| (2,4) | (2,4) | (2,1) | (3,2) | O | (0,0) | (4,0) | (1,0) | (3,3) |
| (3,2) | (3,2) | (3,3) | (2,4) | (1,0) | (4,0) | (0,0) | O | (2,1) |
| (3,3) | (3,3) | (3,2) | (2,1) | (4,0) | (1,0) | O | (0,0) | (2,4) |
| (4,0) | (4,0) | (1,0) | (0,0) | (3,2) | (3,3) | (2,1) | (2,4) | O |

The tests compare all 64 entries with a separate `C4 x C2` table oracle. Its
coordinate dictionary is fixed by `G=(2,1)` and `H=(1,0)`: the tangent at G has
slope 3 and gives `2G=(0,0)`; the chord through G,H has slope 1 and gives
`G+H=(3,3)`; the horizontal chord through `(0,0),H` gives `(4,0)`; inversion
negates y. The resulting dictionary maps `(i,j)` to `iG+jH` and builds expected
entries by integer addition modulo 4 and 2. It does not call the implementation's
addition, inverse, enumeration or auditor to compute expected entries. This
oracle is regression data with an explicit mathematical interpretation, not
a Lean proof of that interpretation.

The exhaustive audit uses every point in the independently enumerable F5
carrier. It does not accept a caller-selected sample or subset. It checks 64
ordered closure cases, 512 associativity triples, 64 commutativity pairs, and
8 cases each for left/right identity and left/right inverse. All pass for the
reference operation. `check_f5_group` reconstructs the table and all checks;
it never accepts a caller-supplied success report as evidence.

### Why membership is insufficient

The demo includes an intentionally incorrect `slope_only_mutant`: it preserves
identity handling but replaces all affine exceptional branches with slope
formulas evaluated using total inversion. For `P=(0,0)` it computes
`lambda=(-1)*inv0(0)=0` and returns **P instead of O**, over both F5 and QQ.
P still satisfies the curve equation, but `P+(-P)=O` fails. Replaying an addition
claim with that on-curve result is rejected as `ADDITION_MISMATCH`.

The unrestricted mutation does **not** preserve membership everywhere: doubling
`(1,0)` over F5 gives the off-curve `(3,0)`. The regression records that fact
rather than claiming all 64 naive outputs pass membership.

For the stronger negative control, `isolated_zero_torsion_mutant` substitutes
that same slope-only formula **only for P+P**, leaving all other entries correct:

| Property | Correct addition | Isolated slope mutation |
| --- | --- | --- |
| Closure / membership | 64/64 pass | 64/64 pass |
| Left/right identity | 8/8 each pass | 8/8 each pass |
| Left/right inverse | 8/8 each pass | 1 failure each, at P |
| Commutativity | 64/64 pass | 64/64 pass |
| Associativity | 512/512 pass | 24 failures among 512 triples |

For `H=(1,0)`, writing the mutated operation as `*`, a concrete witness is
`(P*P)*H=(4,0)` but `P*(P*H)=H`. Every intermediate point is on the curve.
The group check rejects this operation with `GROUP_LAW_FAILURE`.

### Nominal subjects and evidence replay

`Field`, `Curve`, and `Model` are separate immutable in-process handles with
object identity, not structural equality. Their names are display labels only.
Constructing another handle with exactly the same label and equation still
creates a distinct subject. A point retains its model, which retains its curve
and coefficient field. Even O retains these indices. Neither coefficient
equality, equal coordinates, nor an isomorphic presentation authorizes mixing.

Model evidence binds the discriminant to that presentation. Membership evidence
binds its point and exact residual. Addition evidence binds the exact model,
ordered input points, result, branch, denominator and slope. Every evidence check
recomputes the requested arithmetic and compares its subject and payload;
points and evidence from another field, curve, presentation or input pair are
rejected. Both input points are checked before identity shortcuts. Tests also
reject substituted on-curve results, forged denominators, altered branch names,
bad residuals, foreign result points and Boolean scalar claims.

This is an in-process reference API, not serialization of declaration authority
or a hostile-Python security boundary. Bypassing frozen dataclasses or changing
the Python implementation is outside its trust model. Rebuilding a claim for
a new subject and recomputing every obligation is a fresh reference check, not
transport of the old evidence. The JSON report is an observation with display
labels; it cannot be imported as nominal authority. `Model` denotes a coordinate
presentation here; it is **not** the future named `Group` model.

### Verification and integration obligations

| Layer | Established here | Remaining obligation |
| --- | --- | --- |
| Exact reference arithmetic | Canonical F5 / Fraction computations; explicit exception branches; QQ boundary `2(0,0)=O`; discriminants 4 and 64 | No general field, general curve or general rational-point API |
| Finite group laws | The complete F5 table, all listed laws, independent expected table and mutation witnesses | No uniform theorem over bases, families or arbitrary points |
| Lean mathematical semantics | `inv0(0)=0` follows the pinned definition's convention | Formalize this exact carrier/operation and prove branch completeness, nonzero-denominator applicability, membership preservation and group laws; connect the reference to those definitions |
| Named `Group` model | Nominal subject checks are exercised in Python | Bind the actual carrier, chosen operation, owner/declaration identity and Lean evidence to one named structure (#204); no coordinate-based model conflation or reuse of stale evidence |
| Accepted Vastitas Core | No source, IR, checker or code-generation changes | Resolve actual declarations and endpoints through the existing checkers; independently validate source/typed-IR/direct forged-Core cases; prove the relation for the **exact returned Core** and executable operations |
| Scheme and base change | A fixed short-model point representation and explicit infinity | Relate points to `Point<E,T>` with the geometric test object and base map; prove the relevant structural maps and any transport instead of treating a field marker as T |
| Native execution | Python regressions only | Runtime/native refinement and performance measurements remain separate from reference checks and kernel proofs |

Future Lean work must use the actual implementation definitions and preserve
the existing kernel/oracle boundary; a separately copied mathematical model
does not establish acceptance of the compiled operation. This work adds neither
a ninth Domain Checker nor an elliptic compiler opcode. The finite reports do
not discharge #253's full acceptance checklist.

General rings, arbitrary bases, general Weierstrass equations in characteristics
2 or 3, reduction/base-change machinery, model isomorphisms, scalar-multiplication
APIs, cryptographic subgroup approval and constant-time guarantees are outside
this reference. The Python branches and arithmetic make no constant-time claim.
