# Finite polynomial integral enclosure reference (#293)

This is an executable **Python reference verifier and regression suite** for
[#293](https://github.com/MGYamada/Vastitas/issues/293). It checks a supplied finite
certificate for a rational polynomial interpreted as a function on the real line.
It does not implement the proposed `std::validated::integral` public API, amend
ADR 0001, complete #293, or establish Lean/Core/native correctness.

This reference depends on the common arithmetic introduced in
[PR #281](https://github.com/MGYamada/Vastitas/pull/281). It imports that PR's shared
`rational_polynomial_reference.Poly` with **explicit arity 1**. There is no second
polynomial representation. The data-only exact JSON codecs are reused from
`sos_reference`; its SOS acceptance algorithm is not an integral proof route.
The shared arithmetic, SOS verifier and symplectic consumer are unchanged.

## Run

Python 3.10+ and its standard library suffice.

```sh
python3 -m unittest discover -s scripts -p 'test_integral_reference.py' -v
python3 scripts/demo_integral_reference.py
python3 scripts/demo_integral_reference.py --write-dir /tmp/vastitas-integral
python3 scripts/integral_reference.py \
  /tmp/vastitas-integral/coarse_goal_unmet.request.json \
  /tmp/vastitas-integral/coarse_goal_unmet.certificate.json
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/check_boundaries.py
git diff --check
```

Existing CI discovers `scripts/test_*.py`, including the new tests. The demo's
principal candidates and expected totals are hand-supplied; it performs no
partition, approximation or error-bound search.

Validation recorded on 2026-10-31 JST against the dependency head above: all
39 new integral regressions passed. Full Python discovery ran 274 tests:
273 passed and one existing live diagnostic integration test was skipped because
the Rust CLI and Lean kernel were not built. The demo, dependency-boundary check
and staged whitespace check also passed. No Lean build or native error test is
claimed for this Python-only change.

| File | Responsibility |
| --- | --- |
| [integral_reference.py](../scripts/integral_reference.py) | Exact integration, partition/error/totals checks, independent target binding and strict JSON CLI |
| [demo_integral_reference.py](../scripts/demo_integral_reference.py) | Reproducible candidates and separate request/certificate JSON files |
| [test_integral_reference.py](../scripts/test_integral_reference.py) | Mathematical examples, mutation regressions, wire validation and CLI outcomes |

## Fixed interpretation and inputs

The only admitted function representation is an actual canonical `Poly` in
`QQ[x]`, interpreted via the fixed `QQ-to-R-polynomial/v1` embedding. Its meaning
is the polynomial's exact coefficients, not a callback, string expression,
producer-controlled model interpretation or a sample list. Integration uses the
ordinary real Lebesgue measure (`real-lebesgue/v1`) over a finite closed interval
with rational endpoints `a <= b`. No custom measures or orientation reversal
are admitted.

The independent `Request` binds environment, domain and variable IDs, function
ID **and revision and full polynomial**, interval, scalar interpretation and
measure. It also carries an optional positive rational absolute-radius goal.
The `Certificate` repeats the full target for comparison and contains an ordered
tuple of cells and claimed totals. A cell contains its interval, approximation
polynomial, exact `delta`, proof interval and proof-form discriminator.

`polynomial_integrability` is a structural reference check: concrete real
polynomials are continuous and hence integrable on the specified compact
interval. No input field can grant this property to another function class.
Missing polynomial data, a callback/expression, or additional `continuous` or
`integrable` tags are rejected by the schema. This restriction also applies to
zero-length intervals. A failed certificate never asserts non-integrability.
The corresponding mathematical results and their connection to executable
checks still require Lean proofs.

Nominal strings are synthetic reference labels, not authenticated source/Core
identities. The caller must supply the request independently of the certificate.
Changing both copies changes the requested statement; it does not authenticate
the changed source. Both copies agreeing on an unsupported measure or scalar
profile still fails. The reference does not defend against arbitrary Python
code mutating frozen objects through reflection.

## Independent verification stages

| Stage | Operation |
| --- | --- |
| Binding and profile | Compare the complete targets, enforce the fixed interpretation and require `a <= b`. Failure leaves dependent checks `not_checked`. |
| Polynomial integrability | Select only the concrete polynomial-on-compact-real-interval route; no caller continuity evidence. |
| Partition | Check the exact supplied order, positive cell lengths, initial/final endpoints and equality of each adjacent endpoint. Never sort, fill gaps or trim overlaps. |
| Local error | Reconstruct `d_i = f - p_i` coefficientwise, require the proof interval to equal the cell, check nonnegative `delta_i`, and run the supported full-interval bound check. |
| Polynomial integrals | Integrate each `p_i` by the rational coefficient rule and exact endpoint evaluation; compare the complete ordered vector of claimed `q_i`. |
| Center `q` | Sum **recomputed** `q_i`, independently of the claimed local values and total. |
| Radius `E` | Recompute `sum(length_i * delta_i)`, independently of the claimed radius. |
| Enclosure `B` | Compare the claimed endpoints to `[recomputed q - E, recomputed q + E]`, never to a combination of untrusted totals. |

After the prerequisites pass, partition, local error and aggregate comparisons
have separate diagnostics. For example, a gap can coexist with correct local
bounds and exact arithmetic; it still forbids an artifact. A reversed cell
blocks its aggregate calculation. A negative delta, unsupported proof, failed
check or unperformed check also forbids an artifact.

`recompute_totals` is only arithmetic. Diagnostic `recomputed` values in a
rejected report are **not** certified enclosures. Only successful `verify`
constructs a `ReferenceEnclosure` from the independent target, exact cells and
recomputed totals. Python result objects are reference data, not capability
tokens or a production evidence API.

For `a = b`, the canonical partition is empty; the local integral vector is
empty, `q = E = 0` and `B = [0,0]`. Nonempty partitions, including a degenerate
cell `[a,a]`, are rejected. Zero-length cells in a positive interval are also
rejected. Adjacent closed cells may share their single endpoint: real Lebesgue
measure assigns that singleton zero mass.

## Supported local proof

The sole discriminator is `quadratic-extrema/v1`. It selects an actual
calculation, not a trusted proof tag. The checker first computes the difference
polynomial and rejects degree greater than two. For

```math
d(x)=Ax^2+Bx+C,
```

it evaluates both endpoints and, if `A != 0` and the stationary point lies
strictly inside the cell, `-B/(2A)`. The largest absolute value at these points
must be at most `delta`. Constant, zero and linear differences need only their
endpoints. The degree limit is on **the difference**: higher-degree `f` and
`p_i` are supported when their high-degree terms cancel exactly.

These candidates exhaust the extrema for this polynomial class. This is not a
rule admitting arbitrary finite samples. The reduction itself is a pending
mathematical proof obligation. Degree-three-or-higher differences, endpoint or
finite-sample certificates, SOS, Taylor, interval-extension and native/Float
certificates are unsupported, even if the submitted bound happens to be true.
No success is inferred from a solver flag or numerical convergence.

## Validity and accuracy

| CLI status | Exit | Artifact | Accuracy status |
| --- | --- | --- | --- |
| `accepted_reference` | 0 | Returned reference enclosure | `GoalMet`, `GoalUnmet`, or `NotRequested` |
| `rejected_reference` | 1 | None | `NotEvaluated` |
| `invalid_reference_input` | 2 | None | `NotEvaluated` |

The optional goal is `E <= epsilon`, with `epsilon > 0`. Equality meets the goal;
it is the **radius**, not the full width, that is compared. An accepted wide
interval remains accepted with `GoalUnmet`, including CLI exit zero. Changing
the requested goal cannot change the target or enclosure.

Strict JSON uses the existing polynomial wire format and rational pairs
`[numerator, positive_denominator]`; an interval is a pair of such rationals.
Unknown/missing fields, duplicate keys or monomials, invalid exponents, Boolean
integers, float literals (even `0.0`), NaN/Infinity and zero denominators cannot
produce acceptance. Inputs and calculations use arbitrary-precision integers
and `Fraction`. Finite inputs can exhaust resources: no production resource
bound or completeness claim is made. Caught allocation/recursion failures exit
without an artifact; process termination is never a successful result.

## Regressions

For `f(x)=x^2` on `[0,1]`, with requested radius `1/16`:

| Supplied candidate | Recomputed `q` | `E` | `B` | Reference result |
| --- | --- | --- | --- | --- |
| `p=x`, `delta=1/4` | `1/2` | `1/4` | `[1/4,3/4]` | Accepted, `GoalUnmet` |
| Two cells; `p_0=x/2`, `p_1=3x/2-1/2`, both `delta=1/16` | `3/8` | `1/16` | `[5/16,7/16]` | Accepted, `GoalMet` |
| `p=x^2`, `delta=0` | `1/3` | `0` | `[1/3,1/3]` | Accepted, `GoalMet` |
| `p=x`, `delta=1/8` with internally consistent totals | `1/2` | `1/8` | No artifact | Reject: error is `1/4` at `x=1/2` |

The endpoint counterexample `16*x^2*(1-x)^2` has endpoint values zero and exact
integral `8/15`. An endpoint-only certificate is rejected. Relabelling it with
the supported proof discriminator still rejects its degree-four difference.

Other regressions cover negative delta, an invalid bound differing by `10^-20`
that float conversion loses, smaller proof regions, gaps/overlaps/ordering,
missing endpoints, unequal cell lengths, zero intervals, subdivision preserving
the original bound, stale revisions, changed coefficients, wrong measure/domain,
swapped local integrals with unchanged sum, coordinated forged totals, and
nonpolynomial functions with fabricated continuity/integrability tags.

Polynomial-integration tests include a test-only independent Simpson identity
for a finite family of quadratics, exact hand calculations at negative endpoints,
high degree, differentiating the computed primitive and finite additivity.
These tests provide finite regression evidence, not a universal theorem.

## Independent mathematics and unfinished connections

Define the semantic target independently of any checker return value. For real
continuous `f` on `[a,b]`, a valid finite partition and polynomial approximants
with `abs(f(x)-p_i(x)) <= delta_i` on their whole cells, the mathematical argument
is

```math
\left|\int_a^b f(x)\,dx-q\right|
=\left|\sum_i\int_{x_i}^{x_{i+1}}(f(x)-p_i(x))\,dx\right|
\le\sum_i\int_{x_i}^{x_{i+1}}|f(x)-p_i(x)|\,dx
\le\sum_i(x_{i+1}-x_i)\delta_i=E.
```

Integrability of the summands, finite interval additivity, null shared endpoints,
and the local integral inequality are hypotheses/results to establish, not
consequences of Python's `accepted_reference` string. Verification uses the local
certificates and approximation integrals; it does not compare the result to a
directly computed integral of `f` to replace those obligations.

| Boundary | Status and remaining obligation |
| --- | --- |
| Python reference | Implemented finite constructor/verifier and executable regressions. Python, `Fraction`, codecs and implementation are not formally verified. |
| Independent mathematical theorems | **Pending.** Define real polynomial evaluation and the Lebesgue integral independently; prove polynomial continuity/integrability, coefficient integration, the quadratic extremum reduction, finite additivity and error accumulation, including the empty case. |
| Actual executable checker soundness | **Pending.** Prove the real admitted constructor's arithmetic, decoding, binding and fail-closed checks refine those definitions, and relate its exact returned enclosure to the request. A theorem about a copied Python model would not suffice. |
| Actual accepted Core | **Unconnected.** Derive the target from authenticated source/environment identities, revisions, selected interpretation and the exact returned Core occurrence; preserve/recheck that correspondence across specialization and optimization through the existing public acceptance path. |
| Native error guarantees | **Unconnected.** Establish separate conversion, rounding, accumulation, overflow/exception and backend refinement contracts. Exact rational reference success does not certify a Float/ball implementation. |

Under #285's intended split, the independent mathematics belongs in VastitasMath,
soundness of the actual executable checker in VastitasOracle, and the pinned
mathlib correspondence in VastitasBridge; VastitasKernel stays independent of
Mathlib and VastitasMath. Those are future obligations, not modules or proofs
added by this change. This remains an instance of Checker Soundness, with no
additional constitutional theorem or release gate.

Adaptive quadrature, partition/degree/precision search, arbitrary integrability
decisions, improper integrals, tails, singularities, general measures, complex
contours and higher-dimensional integration are outside this reference.
