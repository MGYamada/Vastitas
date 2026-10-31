# Exact SOS cover reference (#244 / #237)

This is an executable **Python reference calculation with regression tests** for
the first real-polynomial consumer of [#244](https://github.com/MGYamada/Vastitas/issues/244)
and [#237](https://github.com/MGYamada/Vastitas/issues/237). It verifies supplied
certificates for one sufficient condition:

```math
f_i\in\mathbb{Q}[x_1,\ldots,x_n],\qquad
\sum_i f_i^2-\delta=v^T Gv,\quad G\succeq0,\quad \delta\in\mathbb{Q}_{>0}
\quad\Longrightarrow\quad
\mathbb{R}^n=\bigcup_i\{x:f_i(x)\ne0\}.
```

Only **all real affine space**, with `n >= 1`, is supported. The opens here are
the generators' actual cozero sets, not arbitrary user-provided lower opens.
There is no SOS/SDP search, decomposition search, general positivity or cover
decision, constrained Positivstellensatz rule, CAD, smooth/analytic expression
parser, section gluing, or partition-of-unity construction. A rejected candidate
does not refute the cover. A cover need not have a uniform positive lower bound;
this condition is intentionally sufficient, not necessary.

The compiler, Lean kernel, proof oracle and stdlib are unchanged. This is not
Vastitas execution, Lean certification, std admission, or a new Domain Checker.
The implementation was prepared against main
`2d6a86ce4c8a44bd883d879035aa9c924ed8fc71`; it does not complete #244 or #237.

## Run and inspect

Python 3.10+; standard library only. Acceptance uses arbitrary-precision integers
and `fractions.Fraction`; no SymPy, floats, eigenvalues, samples or residual
tolerance. The tests use floats only to exhibit information lost by conversion.

```sh
python3 -m unittest discover -s scripts -p 'test_sos_reference.py' -v
python3 -m unittest discover -s scripts -p 'test_symplectic_reference.py' -v
python3 scripts/demo_sos_reference.py
python3 scripts/demo_sos_reference.py --write-dir /tmp/vastitas-sos
python3 scripts/sos_reference.py \
  /tmp/vastitas-sos/singular_cover.request.json \
  /tmp/vastitas-sos/singular_cover.certificate.json
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/check_boundaries.py
```

| File | Role |
| --- | --- |
| [sos_reference.py](../scripts/sos_reference.py) | Independent request binding, exact checks, strict JSON CLI |
| [rational_polynomial_reference.py](../scripts/rational_polynomial_reference.py) | Shared canonical sparse polynomial arithmetic |
| [demo_sos_reference.py](../scripts/demo_sos_reference.py) | Hand-supplied positive/negative candidates and separate JSON pairs |
| [test_sos_reference.py](../scripts/test_sos_reference.py) | Semantic, mutation, compatibility and wire regressions |

CLI status `accepted_reference` / exit `0` means every reference check passed;
`rejected_reference` / exit `1` means at least one failed or was not checked.
`invalid_input` / exit `2` covers malformed/unsupported input and file/JSON errors.
The JSON report retains the exact independent subject, full candidate and every
check outcome. None of these statuses is production `CheckedDescent` evidence.

## Independent checks and LDL convention

`verify(expected, certificate)` never derives `expected` from the certificate.
It first compares the complete immutable subjects. A mismatch reports
`SUBJECT_MISMATCH`; subsequent checks are `not_checked`, never successful.
For well-shaped, matching subjects the following checks run independently, so
one failure cannot hide the other obligations:

| Check | Requirement / failure code |
| --- | --- |
| `polynomial_identity` | Reconstruct `sum(f_i^2)-delta` from the requested generators and `v^T G v` from **all** Gram entries; compare every coefficient exactly. `POLYNOMIAL_IDENTITY_MISMATCH` |
| `gram_symmetry` | Every `G_ij = G_ji`; do not silently symmetrize. `GRAM_NOT_SYMMETRIC` |
| `ldl_structure` | `L` is unit lower triangular. `NOT_UNIT_LOWER_TRIANGULAR` |
| `ldl_identity` | Every entry of `P G P^T = L diag(d) L^T` agrees exactly. `LDL_IDENTITY_MISMATCH` |
| `diagonal_nonnegative` | Every rational `d_i >= 0`, including zero pivots. `NEGATIVE_DIAGONAL` |
| `positive_delta` | Independently require exact rational `delta > 0`. `DELTA_NOT_POSITIVE` |

For a basis vector of length `m`, the certificate declares a permutation `p` of
`0,...,m-1` and fixes **`P[i,p[i]]=1`**. Thus
`(P G P^T)[i,j]=G[p[i],p[j]]`. The wire `convention` must equal the constant
`PERMUTATION_CONVENTION` in the verifier; inverse-convention data is unsupported.
Tests include non-self-inverse 3-cycles, not just swaps. The diagonal matrix is
represented solely by the vector `d`, so off-diagonal entries are unrepresentable;
submitting a full matrix in that field is rejected. All matrices must have the
basis dimension and all rational entries must be exact.

For `w=P v` and `z=L^T w`, the checked identity implies

```math
v^T Gv=w^T(PGP^T)w=z^T\operatorname{diag}(d)z
=\sum_k d_k z_k^2\ge0.
```

This uses nonnegative rational weights, without computing square roots or
dividing by pivots. Zero pivots, including leading or all-zero diagonals, are
valid. Therefore `sum(f_i(x)^2) >= delta > 0` at every real point, so at least one
`f_i(x)` is nonzero. Polynomial continuity makes these cozero sets open. This is
the mathematical argument the future Lean checker must prove, not a Lean theorem
established by the Python implementation. Over complex numbers ordinary squares
do not have this positivity rule; Zariski spectra are not this real-point space.

## Data, binding and shared polynomials

| Bound component | Exact request data |
| --- | --- |
| Context | Environment, object, real base, chart, selected model and model revision |
| Interpretation | Fixed `QQ-to-R-polynomial/v1` scalar profile and `real-cozero/v1` site |
| Domain | Nominal domain ID, `all_real`, and dimension equal to the variable count |
| Generators | Ordered function IDs, revisions and complete rational polynomial coefficients |
| Polynomial coordinates | Distinct ordered variable IDs and distinct **ordered** basis exponent vectors |
| Lower bound | Exact rational `delta`, including its value, independently of the candidate factors |

The certificate carries the full subject plus `gram`, `permutation`, `lower`,
`diagonal`, and `convention`. Strict JSON rationals are `[numerator, denominator]`
with integer numerator and positive integer denominator. Sparse terms are
`{"powers": [e1, ...], "coefficient": [a,b]}`. Unknown fields, duplicate JSON
keys, duplicate monomials, Boolean integer substitutes, negative/noninteger
exponents, zero denominators, float literals (including `0.0`), NaN/Infinity,
string expressions and solver-success flags are rejected. Coefficients are
normalized with `Fraction`, and zero terms removed after input validation.

The existing symplectic `Poly` was extracted, not duplicated. It now records
arity and rejects mixed-arity arithmetic even for zero polynomials. Sorted sparse
terms give canonical coefficientwise equality; this is a representation order,
not a claimed Gröbner-basis implementation. The explicit Gram basis order is
never sorted or inferred. The legacy default arity remains four, and the
symplectic matrix/domain/derivative audits explicitly enforce that contract.
Its existing JSON format, CLI and regression suite remain supported. No second
production polynomial-ring definition is added to `std::validated`.

**Trust boundary:** nominal IDs are synthetic labels. Comparing them does not
authenticate a source object, model law or returned Core. The interpretation is
the fixed QQ-to-real polynomial evaluation specified here, not whatever an
arbitrary `model_id` string might claim. Rewriting both request and certificate
changes the statement; correctly renaming/reindexing everything can validly
prove a different statement. The API does not authenticate who supplied the
request and does not defend against reflective Python object mutation. Python,
`Fraction`, serialization and this checker remain unproved. Enormous finite
inputs can exhaust resources; no totality, production resource bound or general
denial-of-service resistance is asserted.

## Regression examples

For `f=(x,1-x)`, `delta=1/2`, `v=(1,x)`, the baseline uses

```math
G=\begin{pmatrix}1/2&-1\\-1&2\end{pmatrix},\quad
L=\begin{pmatrix}1&0\\-2&1\end{pmatrix},\quad d=(1/2,0).
```

| Case | Reference outcome |
| --- | --- |
| Baseline singular Gram | Accepts; `sum(f_i^2)-1/2=2(x-1/2)^2` and `rank G=1` |
| Permuted singular Gram; leading zero pivot; rank-zero residual | Accepts with the respective exact factors; strict positive definiteness is unnecessary |
| Subtract `10^-20` from `G_00` | Polynomial and LDL identities fail; determinant is `-2*10^-20`, although every converted float entry matches the original matrix |
| Repair that perturbed matrix's exact LDL | Factor identity passes but its negative diagonal is rejected; repairing the factorization does not prove PSD |
| `f=(x,x)`, `delta=0`, `G=diag(0,2)` | PSD and both identities pass; only strict delta fails. The origin is uncovered |
| Same false cover, positive delta and unchanged Gram | Polynomial identity fails |
| Same false cover, `delta=1/2`, `G=diag(-1/2,2)` with exact factors | Both identities pass; negative diagonal fails |
| Wrong factors / non-unit or non-lower `L` | Different decomposition diagnostics, even when a zero pivot hides a change in the product |
| Antisymmetric Gram perturbation | Polynomial identity may pass; symmetry and LDL checks fail |
| Changed variable/basis order, function coefficient, revision or domain identity | Stale evidence fails binding; rebinding incorrectly reindexed coefficients/basis still fails the polynomial identity |
| Restricted-domain, complex, Zariski or Float-profile evidence | Unsupported, even if both subject copies are relabelled |

Additional regressions exercise multivariate coefficient expansion, all six
three-element permutations, exact tiny coefficient changes, malformed dimensions,
unknown float-residual/eigenvalue flags, JSON round trips and executable CLI exits.
Finite regressions establish observed reference behavior, not universal soundness.

## Remaining Lean and actual-Core obligations

These are proposed proof obligations, **not implemented Lean declarations**.
No `sorry`, custom axiom or success-name string discharges them.

| ID | Obligation |
| --- | --- |
| SOS1 | Give independent `MvPolynomial (Fin n) Q` and real-evaluation semantics. Prove decoding, normalization, arithmetic and coefficient equality checks correct for the actual executable representation. Classify Python as a differential-test oracle unless a separate refinement is proved. |
| SOS2 | Prove the exact permutation convention, symmetry/factor checks and nonnegative diagonal imply PSD and the displayed weighted-square identity, with no invertibility/strict-pivot assumption. |
| SOS3 | Connect reconstruction to the **requested** generators and delta; derive the real uniform lower bound, cozero nonvanishing and openness. Use independent semantic cover definitions, not checker success as the definition of a cover. |
| SOS4 | Prove successful composite checking returns evidence for the exact request and exact candidate. Decode invalid/unsupported inputs fail-closed; production bounds and resource failures must never become success. |
| Core1 | Derive the request from the authenticated environment, selected Lawvere model/operations, coefficient embedding, chart/domain, source occurrence and **actual returned Core**. Synthetic matching tags cannot supply these facts. |
| Core2 | Prove that occurrence of that returned Core denotes these precise `f_i`, variable order and real domain. Retain dependency revisions and authority; reject stale or foreign evidence and preserve/recheck correspondence through specialization and optimization. |
| Core3 | Import the actual executable kernel checker into the proof-only oracle and compose its successful result with SOS1–SOS4 and the existing applicable Domain Checker / independent Core Safety obligations under #184. A proof of a copied checker is insufficient. |

The intended future conclusion, for a production acceptance route that actually
includes this SOS consumer, is evidence indexed by its actual returned Core `C`
and extracted subject `S`, together with
`DenoteCoreGenerators(C, occurrence) = DenoteRequestedGenerators(S)` and
`forall x : R^n, exists i, f_i(x) != 0`. It must retain the checked uniform bound
and the same environment, model, base, domain and occurrence. The current public
acceptance theorem does not have this conclusion.

Cover sufficiency is separate from section descent, overlaps/cocycles, effectivity,
localized reciprocal construction, Ownership/Borrow and native numerical
refinement. This work remains inside the existing **8 Domain Checkers plus
independent Ownership/Borrow** architecture and introduces no version or release
gate. The broader admission, Float/enclosure, mixed-precision, cyclotomic and
constrained-certificate obligations in #244 remain open.
