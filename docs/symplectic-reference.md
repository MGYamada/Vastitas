# Exact polynomial symplectic reference (#211)

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

## Run

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

- [Verifier](../scripts/symplectic_reference.py): exact polynomials, independent
  binding/alternation/exterior-derivative/inverse checks, strict JSON CLI.
- [Examples](../scripts/demo_symplectic_reference.py): named positive and negative
  cases; optional separate request and certificate files.
- [Regressions](../scripts/test_symplectic_reference.py): mathematical examples,
  identity/revision mutations, malformed evidence, and CLI exit codes.

Polynomial arithmetic is shared with the [SOS cover reference](sos-reference.md)
through [rational_polynomial_reference.py](../scripts/rational_polynomial_reference.py).
Its explicit arity generalizes the arithmetic while preserving the four-variable
default API here. The symplectic matrix, domain and derivative-witness audits
still require four variables, including for zero polynomials; the JSON schema
and supported symplectic fragment are unchanged.
The metric-free plane consumer also retains its four-variable ambient ring
(restricted to its first two variables), even when a polynomial is zero.
Shared compatibility regressions live in
[test_rational_polynomial_reference.py](../scripts/test_rational_polynomial_reference.py).

CLI exit codes: `0` accepted **reference** input, `1` rejected reference claim,
`2` malformed/unsupported input or file/JSON error. The JSON report includes the
complete expected subject and separate check outcomes. `not_checked` is never
success. Rejecting an unsupported certificate does not prove its mathematical
claim false.

## Exact fragment and conventions

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

## What is bound and what is trusted

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

## Separate checks and the nonzero boundary

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

## Positive and negative examples

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

## Lean soundness obligations (not proved here)

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

## Actual accepted-Core connection and architecture

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
[`Indexed.Wire.check`](../lean-kernel/VastitasKernel/IndexedAcceptance.lean)
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
