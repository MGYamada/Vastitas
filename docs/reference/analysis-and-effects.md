# Analysis, certificates and random supplies

This chapter describes five [reference models](../appendix/reference-models.md)
from analysis and from effects. Four of them check a finite certificate with
exact rational arithmetic: a tail bound that places a sequence in ℓ², an
enclosure of the integral of a polynomial, a sum-of-squares certificate that
cozero sets cover real affine space, and the agreement of two derivative rules
for one function. The fifth models an explicit supply of random bits. Each is
a Python program with tests under `scripts/`, and none is a part of the
compiler.

| Model | In the compiler |
| --- | --- |
| [ℓ² tail certificates](#l2-tail-reference) | Model only. Planned: [#208](https://github.com/MGYamada/Vastitas/issues/208), [#209](https://github.com/MGYamada/Vastitas/issues/209) |
| [Polynomial integral enclosures](#integral-reference) | Model only. Planned: [#293](https://github.com/MGYamada/Vastitas/issues/293) |
| [SOS covers](#sos-reference) | Model only. Implemented: the [principal opens](../affine-geometry.md#principal-opens) of a presented affine object. The language has no declaration of a cover. Planned: [#244](https://github.com/MGYamada/Vastitas/issues/244), [#237](https://github.com/MGYamada/Vastitas/issues/237) |
| [Random supplies](#rand-reference) | Model only. Planned: [#249](https://github.com/MGYamada/Vastitas/issues/249) |
| [Derivative-rule coherence](#derivative-coherence-reference) | Implemented: the reverse pullback of a polynomial smooth map. The kernel computes its derivative from the polynomial, as [Reverse-pass primitives](../language/smooth-declarations.md#reverse-pass-primitives) specifies, and the [Stage 3 acceptance record](../stage3-acceptance.md) states what is Proved about it. A program cannot declare a derivative rule, so the coherence of two rules is a model only. Planned: [#163](https://github.com/MGYamada/Vastitas/issues/163), [#164](https://github.com/MGYamada/Vastitas/issues/164) |

Each section keeps the record of the change that added its model. Its
statements about the compiler describe the repository at that change.
The sections name three Lean packages of
[#285](https://github.com/MGYamada/Vastitas/issues/285). Of these, the proof
oracle `VastitasOracle` and the mathematical bridge `VastitasBridge` exist,
and [Verification boundaries](../verification.md) describes them.
`VastitasMath` is Planned.

<a id="l2-tail-reference"></a>

## Exact real ℓ² tail-certificate reference

This scoped reference implements two executable certificate rules for
[#208](https://github.com/MGYamada/Vastitas/issues/208) and
[#209](https://github.com/MGYamada/Vastitas/issues/209). It is a Python development
reference, not a public `.vast` feature, a Lean-verified checker, or compiler
acceptance. Neither issue is completed by this increment.

### Representation and mathematical meaning

The two supported **closed definitions**, with indexing starting at zero, are

$$
x_n=\iota(a)\iota(r)^n,\quad a,r\in\mathbb Q,\ |r|<1;
\qquad z_n=\frac{\iota(a)}{n+1},\quad a\in\mathbb Q,
$$

where $\iota:\mathbb Q\hookrightarrow\mathbb R$ is the exact field embedding.
`Fraction` evaluates rational parameters and certificate side conditions;
membership means `Summable (fun n => ‖x n‖ ^ (2 : ℕ))` over **ℝ**. It does not
mean convergence in ℚ, machine-float convergence, or completion of the set of
executable generators. Infinite sums and limits are mathematical denotations,
not runtime folds. No float, numerical tolerance, SymPy, or third-party Python
package is used by this reference.

`Geometric` and `Reciprocal` are the entire admitted definition syntax, not
annotations on arbitrary user callbacks. Their rational parameters are in the
body itself. `PrefixThenConstant` is an evaluable adversarial fixture without a
certificate rule. `Opaque` represents an unresolved definition. This reference
does not certify even a mathematically valid opaque sequence from its name.

### Closed proof rules

For both rules the target is the stronger finite-interval inequality

$$
\forall N\le M,\quad
\sum_{n=N}^{M-1}|x_n|^2\le B(N)-B(M)\le B(N),
\qquad B(N)\ge0,\qquad B(N)\longrightarrow0.
$$

The following are mathematical derivations of the rule schemas. Their Lean
formalization and the soundness of the executable checker are **pending**.
Finite regression tests are not substitutes for these universal derivations.

#### Geometric-square telescope

The certificate proposes `GeometricBound(c, q)` and must match the actual
generator's $q=r^2$. The checker verifies, using rational arithmetic,

$$
q=r^2<1,\qquad c\ge0,\qquad c(1-q)\ge a^2.
$$

Define $B(N)=\iota(c)\iota(q)^N$. Nonnegativity follows from $q=r^2\ge0$.
For every natural $n$,

$$
B(n)-B(n+1)-|x_n|^2
=\bigl(\iota(c)(1-\iota(q))-\iota(a)^2\bigr)\iota(q)^n\ge0.
$$

Summing this identity on an arbitrary finite interval telescopes. Since
$0\le\iota(q)<1$, $B(N)\to0$. The producer chooses $c=a^2/(1-r^2)$, for which
the interval inequality is equality; larger valid coefficients also pass.
The zero-ratio case retains $r^0=1$, so the initial term is not discarded.
Ratios with $|r|\ge1$ are outside this rule, including zero-amplitude cases;
`unsupported` is not a proof of nonmembership.

#### Reciprocal-square comparison

The certificate proposes `ReciprocalBound(c)`. The checker verifies $c\ge a^2$
and defines

$$
B(0)=2\iota(c),\qquad B(N)=\frac{\iota(c)}{N}\quad(N\ge1).
$$

At zero, $B(0)-B(1)-|z_0|^2=\iota(c)-\iota(a)^2\ge0$.
For **every** $n\ge1$,

$$
B(n)-B(n+1)-|z_n|^2
=\frac{(\iota(c)-\iota(a)^2)n+\iota(c)}{n(n+1)^2}\ge0.
$$

All denominators here are strictly positive; the zero index is handled
separately. Arbitrary finite intervals telescope again, and $c/N\to0$ in ℝ.
For $a=c=1$ this specializes to
$1/n-1/(n+1)-1/(n+1)^2=1/[n(n+1)^2]$ and the requested bound $B(0)=2$,
$B(N)=1/N$ for $N\ge1$. This certificate bounds the exact squared norm; it
does not evaluate the infinite reciprocal-square sum.

### Acceptance and evidence binding

[`l2_tail_reference.py`](https://github.com/MGYamada/Vastitas/blob/main/scripts/l2_tail_reference.py) checks the full
definition syntax, rational parameters, rule identifier, bound template, and
algebraic side conditions. It never calls `term`, `finite_tail_square_sum`,
`tail_value`, or the untrusted `propose_certificate` producer. There is no
certificate field for sample observations or a heuristic success bit.

| Outcome | Meaning |
| --- | --- |
| `accepted_reference` | A supported rule's exact side conditions and binding passed; not a Lean proof |
| `invalid_bound` | The proposed bound fails the selected rule's arithmetic conditions; the sequence itself may still be in ℓ² |
| `evidence_mismatch` | Evidence targets a different definition, parameters, bound template, Core, environment, or ruleset |
| `unsupported` | Evidence is missing, the rule/semantic profile is unsupported, or the rule's decay premise is unavailable; no nonmembership conclusion |
| `malformed` | Ill-formed records or non-`Fraction` scalar data, including numerically equal floats and bools |

`Binding` stores the complete `ReferenceCore`, complete fixture `Environment`,
and ruleset version. `ReferenceCore` includes the nominal definition identity,
definition revision, and full closed body. The environment includes the scalar
profile and immutable dependency revisions, rejecting duplicate dependency
names. Full structural equality is checked, rather than a supplied hash or
equal finite observations. Even a distinct definition with identical values or
opposite geometric ratio cannot borrow the original evidence.

The accepted record contains the exact Core/environment arguments returned by
this reference check. `audit_acceptance` replays checking against the consumer's
current Core/environment and rejects a changed returned record. Public Python
dataclass construction does not create proof authority. A caller who changes
both a definition and its certificate must pass the rule conditions anew.

These are **reference** bindings. They neither authenticate a source snapshot
nor establish that an actual compiled generator has this definition. Production
evidence must satisfy the independent compiler obligations below.

### Lean semantic propositions to establish

The following Lean-shaped specification defines **proof obligations**, not
inhabited proofs. It is documentation, has not been Lean-built, and introduces
no `sorry`, custom axiom, or executable compiler import. A future proof module
belongs in `lean/`, with the actual executable checker imported from
`lean-kernel/` once implemented there.

```lean
import Mathlib.Analysis.Normed.Lp.lpSpace

open scoped BigOperators ENNReal
open Filter

structure TailEvidence (x B : ℕ → ℝ) : Prop where
  nonneg : ∀ N, 0 ≤ B N
  finiteTail : ∀ N M, N ≤ M →
    (∑ n ∈ Finset.Ico N M, ‖x n‖ ^ (2 : ℕ)) ≤ B N
  vanishes : Tendsto B atTop (nhds 0)

def TailToL2SoundnessGoal : Prop :=
  ∀ x B : ℕ → ℝ, TailEvidence x B →
    Summable (fun n => ‖x n‖ ^ (2 : ℕ)) ∧
    Memℓp x (2 : ℝ≥0∞) ∧
    (∀ N, (∑' k : ℕ, ‖x (N + k)‖ ^ (2 : ℕ)) ≤ B N) ∧
    Tendsto (fun N => ∑' k : ℕ, ‖x (N + k)‖ ^ (2 : ℕ)) atTop (nhds 0)

def GeometricRuleSoundnessGoal : Prop :=
  ∀ a r c : ℚ, r^2 < 1 → 0 ≤ c → a^2 ≤ c * (1 - r^2) →
    TailEvidence (fun n => (a : ℝ) * (r : ℝ)^n)
      (fun N => (c : ℝ) * ((r : ℝ)^2)^N)

def ReciprocalRuleSoundnessGoal : Prop :=
  ∀ a c : ℚ, a^2 ≤ c →
    TailEvidence (fun n => (a : ℝ) / ((n : ℝ) + 1))
      (fun N => if N = 0 then 2 * (c : ℝ) else (c : ℝ) / (N : ℝ))
```

Proof route for `TailToL2SoundnessGoal`:

1. Squares are nonnegative. `finiteTail 0 M` bounds all initial partial sums
   by the finite real number `B 0`. Monotone bounded convergence in ℝ gives
   summability. Equivalently, dominate any finite set by an initial interval
   and apply the nonnegative-sum criterion. **For this implication alone,
   `B(N) → 0` is stronger than necessary.**
2. The pinned mathlib `memℓp_gen_iff` relates `Memℓp x 2` to summability of
   `‖x n‖ ^ (2 : ℝ≥0∞).toReal`. Prove that this real power agrees with the
   natural square; do not silently substitute one exponent type for the other.
   An `lp (fun _ : ℕ => ℝ) 2` value can then pair `x` with that membership proof.
3. For each fixed `N`, pass to the limit in the finite shifted sums, using
   summability, to bound the actual infinite tail by `B N`. Nonnegativity and
   `vanishes` give the residual limit by squeezing. Alternatively, the original
   finite-tail bound and vanishing majorant directly give the Cauchy criterion
   for partial sums in the complete field ℝ.

This uses completeness of **ℝ**; it does not establish completeness of abstract
ℓ², or of executable/certificate-bearing representations. Arbitrary abstract
ℓ² members may use general summability proofs without an executable majorant.

Semantic API checked against the repository's pinned mathlib commit
[`56a005855ea17e0b0958f73ec801ae140b0a1679`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Normed/Lp/lpSpace.lean):
`Memℓp`, `memℓp_gen_iff`, `memℓp_gen'`, and `lp`. The
[rendered documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Lp/lpSpace.html)
can track a newer revision. Inspecting these definitions is not a Lean build.

### Actual returned-Core integration obligation

At the inspected main commit `f56edd4be0010312c24a13bd66a6e43521638a19`,
`VastitasKernel.Indexed.Core.Term` has no infinite-sequence/Hilbert constructor.
For protocol 7, an actual `Wire.CheckedInput json requireMain` retains
`accepted.checked.executable.core.module`. The existing
`VastitasOracle.IndexedWire.codegen_input` theorem connects that exact module
to `accepted.checked.executable.lowered.module`. It proves no tail theorem.
This reference changes neither that Core nor the public wire protocol.

The future attachment checker must discharge all of the following, using
[#184](https://github.com/MGYamada/Vastitas/issues/184)'s existing global boundary:

1. **Same accepted program and environment.** Let `C` be the actual returned
   executable Core above, and `E` its final validated source/dependency,
   declaration, nominal-identity, dispatch, coefficient, and evidence context.
   Resolve a claimed generator occurrence from `C` under `E`; independently
   recover its exact definition and parameter substitution. The frontend
   cannot supply the closed reference definition as an unchecked label.
2. **Same generator at every index.** Prove the semantic bridge
   `∀ n, denoteCoreGenerator E C occurrence n = denoteClosedDefinition d params n`.
   Connect source elaboration and the productive iterator representation to
   that denotation. Equality of names, values on a prefix, or squared values
   alone is not this bridge. The theorem must cover actual selected definitions.
3. **Actual executable acceptance.** Implement a small checker in `lean-kernel/`
   and prove, in `lean/`, that its actual acceptance equation implies matched
   generator/bound/rule/environment and `TailEvidence` for the independently
   defined denotation. Import the real implementation, not a second Boolean
   model, and prove exact rational-to-real arithmetic correspondence.
4. **Exact return and ledger attachment.** A successful call must retain
   `attachment.core = C`, `attachment.environment = E`, and the resolved
   occurrence, parameters, coefficient profile, rule revision and dependencies.
   For **each actual membership obligation** in the ledger, conclude
   `Memℓp (denoteCoreGenerator E attachment.core occurrence) 2` from its checked
   evidence. Do not merely prove that some other generator is summable. The
   caller must consume this attachment with the same Core sent to codegen.
5. **Invalidation and transformations.** Reject stale evidence when any of the
   bound inputs changes. Each optimizer/rewriter must either transport the
   evidence through a proved semantic-preservation relation for its actual
   returned Core or recheck it. General kernel-checked summability proofs may
   provide another bridge, but unknown evidence remains unresolved here.

The reference mutation tests exercise analogous record constraints only; they
do not discharge these compiler obligations. Production proof authority must
not be a serialized `accepted_reference` field, a caller-created dataclass, a
dependency string, or an unauthenticated digest. A future axiom audit must cover
the actual checker theorem, rule theorems, semantic bridge, and return/ledger
composition, without unproved analytic or native-execution assumptions hidden
behind an acceptance predicate.

### Reproduction and verification status

```sh
python3 -m unittest discover -s scripts -p 'test_l2_tail_reference.py' -v
python3 scripts/demo_l2_tail_reference.py
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/check_boundaries.py
```

The 28 focused tests include 1,617 exact geometric interval identities and
1,617 reciprocal interval inequalities (`0 ≤ N ≤ 32`, `N ≤ M ≤ 64`), signed
rational amplitudes/ratios, zero amplitudes/ratios, loose bounds, missing
evidence, stale Core/environment/definition/parameter/rule records, and forged
acceptance records. They reproduce the common first-eight-term squared norm
`21845/16384`, the invalid borrowed `B(8) = 1/49152` against a term of square 1,
and the missing `4/3` factor counterexample `5/4 > 1`.

One geometric coefficient is understated on purpose: `4/3 - 10^(-100)`.
Every sampled interval still obeys its weak finite bound, yet the exact rule
rejects it. Tests also disable the observation functions and candidate producer
while checking certificates. These regressions guard against sampling-based
acceptance; they do not establish universal analytic statements.

| Layer | Status in this increment |
| --- | --- |
| Closed rational rule checking and reference return/snapshot audit | Implemented; focused tests executed |
| Finite rational observations | Executed as regressions only |
| General analytic implication and two rule soundness propositions | Specified above; no Lean proof or build |
| Actual compiler generator extraction, returned-Core/ledger composition | Pending; reference records are not compiler certificates |
| Ordinary compiler dependency isolation | No dependency/import changes; boundary checker executed; existing no-mathlib CI retained |
| ℓ² completeness, general inner products/operators, iterator memory safety | Outside this fragment; no guarantee added |

Existing CI already discovers `scripts/test_*.py`. Python remains development
infrastructure. Neither ordinary compilation nor generated programs invoke
this reference or mathlib. A future Lean implementation must keep executable
checks in the mathlib-free kernel and analysis proofs in the proof-only oracle;
it must compose the frozen 8+1 architecture rather than add another checker.

<a id="integral-reference"></a>

## Finite polynomial integral enclosure reference (#293)

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

### Run

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

Existing CI discovers `scripts/test_*.py`, including these tests. The demo's
principal candidates and expected totals are hand-supplied; it performs no
partition, approximation or error-bound search.

Validation recorded on 2026-10-31 JST against the dependency head above: all
39 integral regressions passed. Full Python discovery ran 274 tests:
273 passed and one existing live diagnostic integration test was skipped because
the Rust CLI and Lean kernel were not built. The demo, dependency-boundary check
and staged whitespace check also passed. No Lean build or native error test is
claimed for this Python-only change.

| File | Responsibility |
| --- | --- |
| [integral_reference.py](https://github.com/MGYamada/Vastitas/blob/main/scripts/integral_reference.py) | Exact integration, partition/error/totals checks, independent target binding and strict JSON CLI |
| [demo_integral_reference.py](https://github.com/MGYamada/Vastitas/blob/main/scripts/demo_integral_reference.py) | Reproducible candidates and separate request/certificate JSON files |
| [test_integral_reference.py](https://github.com/MGYamada/Vastitas/blob/main/scripts/test_integral_reference.py) | Mathematical examples, mutation regressions, wire validation and CLI outcomes |

### Fixed interpretation and inputs

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

### Independent verification stages

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

### Supported local proof

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

### Validity and accuracy

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

### Regressions

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

### Independent mathematics and unfinished connections

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

<a id="sos-reference"></a>

## Exact SOS cover reference (#244 / #237)

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
Vastitas execution, Lean certification or std admission, and it adds no Domain Checker.
The implementation was prepared against main
`2d6a86ce4c8a44bd883d879035aa9c924ed8fc71`; it does not complete #244 or #237.

### Run and inspect

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
| [sos_reference.py](https://github.com/MGYamada/Vastitas/blob/main/scripts/sos_reference.py) | Independent request binding, exact checks, strict JSON CLI |
| [rational_polynomial_reference.py](https://github.com/MGYamada/Vastitas/blob/main/scripts/rational_polynomial_reference.py) | Shared canonical sparse polynomial arithmetic |
| [demo_sos_reference.py](https://github.com/MGYamada/Vastitas/blob/main/scripts/demo_sos_reference.py) | Hand-supplied positive/negative candidates and separate JSON pairs |
| [test_sos_reference.py](https://github.com/MGYamada/Vastitas/blob/main/scripts/test_sos_reference.py) | Semantic, mutation, compatibility and wire regressions |

CLI status `accepted_reference` / exit `0` means every reference check passed;
`rejected_reference` / exit `1` means at least one failed or was not checked.
`invalid_input` / exit `2` covers malformed/unsupported input and file/JSON errors.
The JSON report retains the exact independent subject, full candidate and every
check outcome. None of these statuses is production `CheckedDescent` evidence.

### Independent checks and LDL convention

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

### Data, binding and shared polynomials

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

The existing symplectic `Poly` was extracted, not duplicated. The shared class
records arity and rejects mixed-arity arithmetic even for zero polynomials. Sorted sparse
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

### Regression examples

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

### Remaining Lean and actual-Core obligations

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

The intended future conclusion, for a production acceptance route that
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

<a id="rand-reference"></a>

## Finite random-supply reference

This executable Python reference tests the associativity and reproducibility
foundations of [#249](https://github.com/MGYamada/Vastitas/issues/249). It is not
public `.vast` syntax, a production sampler, compiler acceptance, or a Lean proof.
It does not complete #249. No PRNG, entropy source, Float transform, or
Box–Muller implementation is selected or introduced.

Run from the repository root, using only Python's standard library:

```sh
python3 scripts/demo_rand_reference.py
python3 -m unittest discover -s scripts -p 'test_rand_reference.py' -v
```

The existing CI command `python3 -m unittest discover -s scripts -p 'test_*.py'`
discovers these tests. Implementation: [rand_reference.py](https://github.com/MGYamada/Vastitas/blob/main/scripts/rand_reference.py);
regressions: [test_rand_reference.py](https://github.com/MGYamada/Vastitas/blob/main/scripts/test_rand_reference.py).

### Responsibility boundaries

| Layer | Owner and scope |
| --- | --- |
| Mathematical Monad | `std::category::Monad` ([#199](https://github.com/MGYamada/Vastitas/issues/199)): endofunctor, unit, multiplication, naturality, and law evidence. |
| Pure probability | `std::distribution` ([#248](https://github.com/MGYamada/Vastitas/issues/248)): measures and kernels; the canonical mathematical Giry instance. `FiniteDist` models only finite rational measures here. |
| Execution interface | `monad::kleisli` ([#206](https://github.com/MGYamada/Vastitas/issues/206)): derive the extension/triple and sequencing interface from the same certified mathematical instance. No second law authority. |
| Sampling realization | `monad::rand` (#249): explicit supply, sequential state threading, separately requested splitting, and logical address ownership. |

`compose_dist` is a finite mathematical sum/product calculation, not a proposed
operational `std` API. Python callbacks and closures are convenient test notation;
they do not relax Vastitas's closure-free/ownership rules. No `State` or `Except`
package, Domain Checker, or named certified Monad instance is installed by
this reference.

### State transitions and explicit splitting

`Supply` stores immutable bit/address tuples and a cursor. A successful read
returns the bit, the advanced supply, and a `Read(address, bit, consumed=True)`
audit event. Sequential `bind` passes the exact returned supply to its
continuation, without splitting. It concatenates audit events in execution order.
Tests compare the entire result, including output, remaining bits/position, and
trace, rather than only the final distribution.

The intended successful state transition is `S -> (A, S)`. To model finite
exhaustion explicitly, this reference adds an absorbing `Exhausted` result that
retains the current supply, requested capacity, and consumed-prefix trace. This
is a failure-and-trace extension of State, not a total finite-bit sampler for
arbitrarily many draws. Later continuations do not run after exhaustion. Ordinary
Python exceptions are outside the modeled outcomes and propagate as errors.

`split_at(k)` is an explicit operation: the next `k` remaining bits go to the
left child and all others to the right, with their original addresses. The
returned parent has no available bits. No bits are duplicated, omitted, or
renumbered; already-consumed bits are excluded. Insufficient capacity fails
without a partial partition. Empty children are permitted. This fixed contiguous
partition is a finite fixture, not a production key-derivation algorithm.

Supply snapshots remain inspectable and copyable Python values so that the
negative State examples and extensional comparisons can be expressed. Retaining
the old parent or manually rebuilding a child is **not prevented in Python**.
Production opacity, legal moves, disjoint-domain ownership, and compiler checking
remain separate obligations. The reference does not certify arbitrary callbacks
as admissible samplers.

`bad_split_bind` is incorrect on purpose: it splits by syntax-tree position. Its
two bracketings produce `(LL, LR, R)` and `(L, RL, RR)`. A single six-address
bit table witnesses different outputs, while exhaustive uniform enumeration of
that same table gives the same three-bit output law for both. Equal distributions
therefore do not establish identical fixed-supply execution.

### Exact finite laws and the independence boundary

`FiniteDist` requires normalized, nonnegative `Fraction` weights and hashable
outcomes. Repeated outcomes are aggregated exactly; floats are rejected.
`uniform_bits(n)` enumerates the declared uniform product measure on `{0,1}^n`,
including the singleton empty supply for `n=0`. Enumeration is capped at 12 bits
because it is exponential. This explicitly chosen probability space is not a
claim about a deterministic seed or any real PRNG.

`execution_law(program, source)` computes the exact finite pushforward into
`Returned(value)` or `Failure.SUPPLY_EXHAUSTED`. Successful `None` remains distinct
from shortage. `output_law` projects to values only when all source mass succeeds;
otherwise it rejects. It never discards failure mass or conditions on success.

For the two-consuming-read example, under the explicitly independent two-bit
source, the finite bind equation agrees with mathematical kernel composition:

```text
P((0,0)) = P((0,1)) = P((1,0)) = P((1,1)) = 1/4.
```

By contrast, two `unsafe_peek_bit` calls reuse the same bit without advancing:

```text
P((0,0)) = P((1,1)) = 1/2;  P((0,1)) = P((1,0)) = 0.
```

Each individual peek has the same fair marginal as a consuming read, but
`P(first == second)` is `1` rather than `1/2`. The peek program still satisfies
the ordinary sequential **State** equations in the finite tests. What fails is
the proposed unrestricted independent-law interpretation.

Correct consumption or disjoint split addresses alone also do not prove source
independence: a source supported on `00` and `11` remains correlated after either
operation. The tests retain this second negative case. A mixed success/shortage
fixture gives each outcome mass `1/2` and cannot be exposed as an output-only law.

For an eventual `law_ideal` morphism, the admissible fragment must use fresh,
independent ideal supply, preserve the required residual-source invariant, and
exclude arbitrary introspection/replay. Measurability and any termination/totality
hypotheses also belong to that theorem. Finite variable-consumption examples
must track remaining capacity; the cursor/remaining length itself may reveal
previous results. The relevant freshness concerns unread bit values conditional
on the permitted consumption history, not independence of the entire cursor
state. This reference tests both fixed and bounded value-dependent consumption
with enough bits; it does not decide admissibility or prove the general morphism.

### Logical address ownership and schedules

`LogicalAddress` is the explicit tuple
`(profile, seed, namespace, logical_index, draw_index)`. The fixed profile name
`finite-logical-address-v1` describes only this reference schema, not a PRNG.
Logical/draw indices are in `[0, 2^32)` with overflow rejected, never wrapped.
The seed is a nonnegative integer label; it is not expanded into random bits.

`LinearKey` is a one-use handle at the level of each Python object. Two separately
constructed handles can consume the **same address**, despite each being used
only once. `AddressBook` additionally owns a finite domain and retains the complete
allocation history for one run. It rejects overlapping domain entries, outside
addresses, and duplicate claims both before and after the first handle is spent.

The scheduling regression fixes a table of eight bits for four logical tasks,
each with two draws. Across all 24 task execution orders, it reconstructs addresses
from task/draw identity and checks the complete task-to-address/value mapping.
Allocation order and physical worker identity are absent from the address.
This tests schedule-independent addressing and lookup, not randomness quality.

All claims in a run must use its single domain owner. The example simulates
schedules sequentially; it is not a thread-safe/distributed allocator. A fresh
book explicitly starts a separate run/replay and does not provide cross-run
deduplication. Python attribute access/copying is not a security or static
linearity boundary. Production disjoint tokens, parallel allocation, intentional
replay policy, and ownership refinement remain future work.

### Evidence ledger and future proof work

| Status | What this increment establishes or leaves open |
| --- | --- |
| Executable finite tests | All eight three-bit supplies; both sequential bracketings including residual state/trace; unit and associativity cases with branching, nonzero cursors and shortage; explicit split; exact rational laws and counterexamples; all 24 task schedules; duplicate/overflow rejection. |
| Conditional mathematical correspondence | Intended `law_ideal` return/bind equations on an admissible fragment under explicit fresh-source and other mathematical hypotheses. No Python return value is evidence for that general theorem. |
| Future Lean proofs | Formalize sequential transitions and error/trace extension, prove unit/associativity extensionally, establish the residual-source invariant and conditional law morphism, prove split-domain disjointness/address uniqueness, and connect actual checked implementation and derived Kleisli evidence to the canonical mathematical Monad. |
| Unsupported here | Production PRNG/version/known-answer vectors, entropy, continuous distributions, Box–Muller, Float/GPU equality, compiler integration, static ownership certification, and general ideal-source independence. |

The finite negative examples refute specific unrestricted claims. Passing the
positive tests is regression evidence for these fixtures, not a universal proof,
an independence certificate, or completion of #199/#206/#248/#249.

<a id="derivative-coherence-reference"></a>

## Derivative-rule coherence reference (#163 / #164 / #192)

This executable **Python reference and specification** distinguishes true
ambient derivatives, derivatives within a set, and explicitly selected
backwards. It refines the design obligations in [#163](https://github.com/MGYamada/Vastitas/issues/163),
[#164](https://github.com/MGYamada/Vastitas/issues/164), and
[#192](https://github.com/MGYamada/Vastitas/issues/192).
It is not production AD, a Lean theorem, an authenticated rule registry,
actual-Core derivative acceptance, or a general differentiability decision
procedure. It claims no checker, release target or CF completion.

The reviewed implementation baseline is
`e026b89cbdbe6ea2f766cde7d18bdd959f48a007`. The examples follow #278's pinned
mathlib semantics, #279's independent proof-route principle, and #285's intended
independent mathematical semantics / Bridge architecture. The latter is not a
claim that the proposed packages or migration existed at that revision.

PR #270 already supplies the [metric reference](geometry.md#metric-reference). This
reference has no metric, musical-map or coordinate-conversion implementation.

The mathematical API review uses mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`, pinned by the baseline lockfile:

- [FDeriv/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Calculus/FDeriv/Basic.lean)
- [FDeriv/Congr.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Calculus/FDeriv/Congr.lean)
- [FDeriv/Comp.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Calculus/FDeriv/Comp.lean)
- [FDeriv/Defs.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Calculus/FDeriv/Defs.lean)
- [TangentCone/Real.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Calculus/TangentCone/Real.lean)

### 1. Three contracts, with explicit scope

Use distinct semantic propositions. The names below are proposed vocabulary,
not implemented public syntax.

| Contract | Mathematical meaning | What does not follow |
| --- | --- | --- |
| `AmbientDerivative(f,x,L)` | `HasFDerivAt f L x` for the declared scalar field, normed spaces and map interpretation | No derivative at another point, no derivative field on an entire region, no native correctness |
| `WithinDerivative(f,S,x,L)` | `HasFDerivWithinAt f L S x`, retaining the actual set/filter | No ambient differentiability and no unrestricted uniqueness without further hypotheses |
| `SelectedBackward(f,x,policy,B)` | The explicit backward program realizes the declared policy/action at its indexed cotangent endpoints | No assertion that `B` is the dual of a true derivative |

`L` is a continuous linear map. In the finite real examples its matrix is `J`;
the backward is the canonical dual `L*(eta) = eta o L`, represented by `J^T eta`.
No metric, gradient, Hermitian identification or implicit conjugation is involved.
Real and complex derivative contracts are not interchangeable.

Keep **the map's domain**, **the set S used for within differentiation**, and
**the set U on which a registered rule is promised to work** as distinct data.
A point theorem is not a `forall x in U` theorem. If the primal is a partial map,
an ambient statement requires a specified interpretation on a neighborhood of x;
an arbitrary extension outside its domain cannot redefine the original map.

Record function/method identity and revision, defining/attaching authority,
environment and mathematical model, scalar field, source/target identities,
domain hypotheses, basepoint x and output f(x), exact linear/backward code,
proof kind, quantifier scope and dependencies. A name, shape, successful sample,
priority, `fderiv` value or producer-supplied checked flag is not this evidence.
Mathlib's total `fderiv`/`fderivWithin` functions include default choices; use
`HasFDerivAt`/`HasFDerivWithinAt` evidence, not the mere availability of a value.

### 2. Direct-versus-composite coherence for true derivatives

Work first over real normed spaces E, F, G. Analogous scalar profiles require
their own correctly typed hypotheses. Let g:E->F, h:F->G, f:E->G and x:E.

#### Ambient rule

Require independently checked witnesses for

```text
HasFDerivAt f L x
HasFDerivAt g A x
HasFDerivAt h B (g x)
f =ᶠ[𝓝 x] h o g
```

The last premise is equality on a neighborhood of x (equality of germs), not
just `f(x) = h(g(x))`. Global equality is sufficient but unnecessary. The chain
rule supplies `HasFDerivAt (h o g) (B.comp A) x`; neighborhood congruence
transports it to f, and uniqueness proves

```text
L = B.comp A
L* = A* o B*.
```

The germ equality also gives `f(x)=h(g(x))`. Retain the corresponding output
fiber transport so both backwards consume a cotangent at the same actual point.
Equality means equality as linear maps, hence for every valid cotangent seed,
not agreement for one seed. The proof does not require global smoothness of f,
g or h; differentiability at the stated points and the local equality suffice.

For two unrelated direct implementations f1 and f2, the same argument uses
`HasFDerivAt f1 L1 x`, `HasFDerivAt f2 L2 x` and their germ equality. Different
nominal objects, scalar structures or charts need explicit valid transports;
equal dimensions do not discharge these premises.

For a reusable derivative field on U, establish these conditions for every
point in the claimed U. Equality of the two derivatives at one x proves only
the pointwise claim. In particular, `2x` and `4x` agree at zero; this cannot
certify the former as the derivative field of `2x²`. Conversely, the scalar
zero *is* the true derivative at zero if proved using a valid point theorem.

#### Within-set rule and uniqueness

The corresponding sufficient premises are

```text
HasFDerivWithinAt f L S x
HasFDerivWithinAt g A S x
HasFDerivWithinAt h B T (g x)
MapsTo g S T                         -- or the appropriate local Tendsto proof
f =ᶠ[𝓝[S] x] h o g
f(x) = h(g(x))
UniqueDiffWithinAt k S x.
```

Public applications also retain required membership witnesses, including x in
S and g(x) in T. The separate basepoint equation is needed by within-congruence;
it is not inferred from an arbitrary punctured or within filter. When x in S
and an adequate relative neighborhood equality imply it, record that derivation.

Chain-rule and congruence give two within derivatives of the same map on S;
`UniqueDiffWithinAt.eq` gives equality of their full continuous linear maps.
Uniqueness on T is not necessary merely to compose given witnesses. If two
rules have different within sets, first justify a common restriction or equality
of their local filters, and then prove uniqueness on that actual comparison
set. Intersecting two domains can destroy uniqueness.

Without `UniqueDiffWithinAt`, the individual within witnesses may still be
valid. Equality on the tangent cone (`HasFDerivWithinAt.unique_on`) is weaker
than equality of the ambient linear maps. Reject an unsupported full-map
coherence claim; do not relabel valid within evidence as false.

#### Promotion to the ambient derivative is a separate rule

The standard sufficient promotion is

```text
HasFDerivWithinAt f L S x + S in 𝓝 x  =>  HasFDerivAt f L x.
```

`IsOpen S` together with `x in S` suffices. `UniqueDiffWithinAt k S x` alone
does not. For `f(x)=|x|`, `S=[0,infinity)`, x=0, the within derivative is uniquely
the slope 1, but there is no ambient derivative at zero. At x=1 this same S is
a neighborhood and the promotion is legitimate. For `S={0}`, arbitrary slopes
are valid within derivatives at zero; neither uniqueness nor promotion holds.

The neighborhood premise is sufficient, not necessary for every possible proof
of ambient differentiability. An independent ambient proof may already exist;
restriction plus within uniqueness can then identify its derivative with L.
A separately proved gluing theorem can also be used with all its premises.
Neither route follows from within uniqueness alone, and an extension theorem
must still establish the required neighborhood agreement with the original map.

### 3. Acceptance, rejected candidates and available proof routes

Distinguish proposing a rule, admitting a registration, resolving an occurrence,
and proving an optimizer rewrite. Preserve diagnostics and proof dependencies.

| Situation | Required outcome |
| --- | --- |
| Two true-derivative routes with the coherence premises above | Establish equality, then either proved implementation may be chosen; retain its provenance. |
| A candidate has only tests, an unsupported hypothesis or an invalid proof | Refuse that candidate's requested certificate. Report missing/failed obligations, not a theorem of non-differentiability. |
| One optional candidate is refused and an independent route proves the exact requested derivative | The occurrence may use the proved route. The refused candidate is not installed or silently upgraded. |
| An explicit required rule/selected policy fails, or an active registry is inconsistent | Fail that request/registration; no silent substitution by a different policy or dropping of a required invalid attachment. |
| Two purported true rules disagree under identical checked premises | Treat as an evidence, binding or implementation inconsistency; no priority/import-order override. |
| A within proof lacks uniqueness | Keep its within status; reject the unproved full-map equality claim. |
| A within proof lacks ambient promotion evidence | Reject ambient promotion; still permit an independent ambient proof if available. |
| A selected backward equals a true derivative numerically | Retain selected status until a separate derivative/correspondence proof is checked. |

The simplest independent-route witness is `g(x)=|x|`, `h(u)=u²` at zero.
The usual ambient chain rule through g is unavailable, while the whole
composite equals x² and has a valid derivative. This follows #279. A true-rule
request can use the whole-function proof; it need not discover a differentiable
factorization or claim that the failed factorization is valid.

### 4. Optimizer consequence (#164)

For a true-derivative context, a certified primal germ equality and valid
ambient derivative evidence on both sides justify equality of pullbacks by
uniqueness. No independently guessed priority between the two rules is needed.
Retain the applicability domain, scalar profile, basepoint/output transports,
and any separate realization/ownership obligations.

For a selected-backward context, primal germ equality does not prove equality
of the selected action. Require policy-aware equality for every admitted
cotangent seed on the claimed domain, including residual dependence; otherwise
reject the rewrite or preserve a barrier. Existing ReLU examples in #164 remain
valid. A true derivative proof for the same primal does not erase an observable
selected policy. Equally, a selected policy never supplies the premises of
`HasFDerivAt.unique`.

The branch `if x == 0 then 0 else x` denotes the identity over R. Its zero
branch is constant only on `{0}`. That branch's within derivative is not a
certificate for the whole function. An exact whole-function equality proof
permits the ambient derivative 1. A separately declared zero-backward policy
remains selected and cannot silently replace this true derivative.

### 5. Executable reference and its limits

Run with Python 3.10+ and no third-party packages:

```sh
python3 -m unittest discover -s scripts -p 'test_derivative_coherence_reference.py' -v
```

The [reference](https://github.com/MGYamada/Vastitas/blob/main/scripts/derivative_coherence_reference.py) and
[regressions](https://github.com/MGYamada/Vastitas/blob/main/scripts/test_derivative_coherence_reference.py) use
`Fraction`, exact polynomial coefficients, a closed domain catalogue and
explicit evidence constructors. No floating tolerances, finite differences,
ForwardDiff invocation or production Vastitas execution are involved.

For `g(x)=(x,x²)`, `h(u,v)=u²+v`, `f(x)=2x²`, the reference independently
checks the direct polynomial Jacobian and composition of checked factor
Jacobians, with exact intermediate basepoint `g(x)` and nominal endpoints.
The shared result is 4x; the dual action is multiplication by 4x. Polynomial
coefficient identities certify the reference's supported symbolic formulas;
the displayed finite basepoint/seed checks are regression observations only.

The branch normalizer has two small rules: for `if x==0`, compare
the exceptional values exactly and then use the other polynomial everywhere;
for `if x>=0`, either both branch polynomials agree identically or an explicit
nonnegative domain chooses that branch. This is not a general branch AD engine.
`square(abs(x))` is constructed branch by branch and normalized to x².

Each admitted `Rule` is bound to one `Context` and basepoint. The polynomial
constructor uses a stronger whole-domain formula check as sufficient evidence;
`point_from` uses an already verified derivative at the same point plus exact
linear-map equality *at that point*. It does not turn its formula into a
derivative field. The promotion constructor is likewise point-scoped.

The domain catalogue records known mathematical facts about R, `{0}`,
`[0,infinity)` and `(-1,1)`; their Lean justification remains pending. This Python
API is an in-process reference, not an authenticated ownership/evidence store
or hostile decoder. Caller-supplied expected identity/policy data must come from
the actual checked environment in production. It exposes no accepted-Core token.

The 22 regression tests cover the required examples plus domain, basepoint,
revision, environment, nominal endpoint and shape mutations. Existing CI's
`python3 -m unittest discover -s scripts -p 'test_*.py'` includes these tests.
Reference test success does not establish Lean proofs or production compiler
acceptance; neither is implemented by these files.

### 6. Required Lean results (separate from reference test success)

These are proof obligations and reviewed API dependencies, not completed
theorems. At the pinned mathlib revision the following building blocks exist:

| Dependency | Location | Role |
| --- | --- | --- |
| `HasFDerivAt.comp` | FDeriv/Comp.lean, line 105 | Ambient chain rule at g(x) |
| `HasFDerivWithinAt.comp`, `.comp_of_tendsto` | FDeriv/Comp.lean, lines 75, 86 | Relative chain rule with MapsTo/local filter premises |
| `HasFDerivAt.congr_of_eventuallyEq` | FDeriv/Congr.lean, line 174 | Transport over an ambient germ equality |
| `HasFDerivWithinAt.congr_of_eventuallyEq` | FDeriv/Congr.lean, line 158 | Relative germ transport with an explicit basepoint equation |
| `HasFDerivAt.unique` | FDeriv/Basic.lean, line 173 | Ambient uniqueness |
| `UniqueDiffWithinAt.eq` | FDeriv/Basic.lean, line 165 | Within uniqueness under its extra premise |
| `HasFDerivWithinAt.singleton` | FDeriv/Basic.lean, line 305 | Any continuous linear candidate on a singleton |
| `HasFDerivWithinAt.hasFDerivAt` | FDeriv/Basic.lean, line 357 | Promotion with S in the ambient neighborhood filter |
| `uniqueDiffWithinAt_Ici` | TangentCone/Real.lean, line 133 | Within uniqueness at the endpoint of a real closed half-line |

Minimal statement/proof sketches, to be elaborated and checked in the pinned
Bridge environment, are:

```lean
-- In real normed spaces E, F, G, with continuous linear maps L, A, B:
-- hf : HasFDerivAt f L x
-- hg : HasFDerivAt g A x
-- hh : HasFDerivAt h B (g x)
-- heq : f =ᶠ[𝓝 x] (h ∘ g)
-- Goal: L = B.comp A
exact hf.unique ((hh.comp x hg).congr_of_eventuallyEq heq)

-- hf : HasFDerivWithinAt f L S x
-- hg : HasFDerivWithinAt g A S x
-- hh : HasFDerivWithinAt h B T (g x)
-- hm : Set.MapsTo g S T
-- heq : f =ᶠ[𝓝[S] x] (h ∘ g)
-- hx : f x = h (g x)
-- hu : UniqueDiffWithinAt ℝ S x
-- Goal: L = B.comp A
exact hu.eq hf ((hh.comp x hg hm).congr_of_eventuallyEq heq hx)

-- hf : HasFDerivWithinAt f L S x; hs : S ∈ 𝓝 x
-- Goal: HasFDerivAt f L x
exact hf.hasFDerivAt hs
```

Required additional proofs are:

1. Real denotation of rational polynomials, exact coefficient normalization,
   differentiation/substitution and the reference's two branch-equality rules.
2. The two concrete derivative routes, the whole-branch identity derivative,
   the point-versus-field distinction for 2x, and the independent derivative of
   `square(abs(x))` despite the unavailable ambient factor rule at zero.
3. The domain facts used by the finite catalogue, including within uniqueness
   on the closed half-line at zero, its failure to be a neighborhood there,
   and singleton nonuniqueness. Keep these as separate propositions.
4. Dualization of linear-map equality and reversed composition, with explicit
   cotangent basepoint transports, for all seeds in the declared finite profile.
5. Independent semantics of selected policies and preservation under a checked
   rewrite. No theorem stating that an arbitrary selected policy is a derivative.
6. Soundness of the **actual** evidence validator and its decoder/registration/
   occurrence binding, using implementation definitions, not this Python model.

Under #285's intended split, reusable propositions belong in `VastitasMath`,
pinned-mathlib models and congruence/uniqueness correspondence in `VastitasBridge`,
and actual-checker soundness in `VastitasOracle`. Ordinary `lean-kernel/` remains
mathlib-free. This does not claim that those packages or migrations existed at
the revision that this section names.

### 7. Actual accepted-Core obligations (#163 / #192)

The current [IndexedAcceptance.lean](https://github.com/MGYamada/Vastitas/blob/e026b89cbdbe6ea2f766cde7d18bdd959f48a007/lean-kernel/VastitasKernel/IndexedAcceptance.lean)
defines `Wire.CheckedInput`, retaining exact decoder and combined-checker
equations. The [IndexedWire oracle](https://github.com/MGYamada/Vastitas/blob/e026b89cbdbe6ea2f766cde7d18bdd959f48a007/lean/VastitasOracle/IndexedWire.lean)
connects actual checked audit/executable Core to typing and finite evaluation;
it explicitly does not prove numerical semantics or native refinement. These
existing guarantees are not derivative-rule acceptance.

A future implementation must establish, for each actual derivative occurrence:

```text
actual acceptance(input, pinned environment, evidence) = returned artifact
  => the occurrence, selected method, primal, domain and evidence are the requested ones
  => the exact returned executable/audit Core satisfies its declared contract
  => every certified pass preserves that contract and its dependencies.
```

For the ambient case, the independent semantic conclusion includes
`HasFDerivAt (denote primalCore) L x` and
`denote backwardCore (eta) = eta o L` at the actual output basepoint, for every
valid eta. For the within case retain S and its distinct property; for selected
backward conclude only the declared policy semantics unless separate derivative
evidence exists. Conditional assumptions remain visible, not silently discharged.

Concrete integration obligations:

- Decode untrusted candidates without deserializing trusted evidence status;
  verify authority and exact subject, model, domain, scalar, point, code and
  theorem identity independently of the producer.
- Connect the mathematical evidence to the actual returned Core and selected
  implementation, including original source mapping, both audit/executable paths,
  inactive or nonwinning registrations where the existing all-body policy applies,
  and any admitted direct Core entry points. Type-correct linear IR alone is insufficient.
- Preserve rejected optional candidates versus required registrations in the
  resolution trace. Do not fabricate successful evidence after falling back.
- Carry primal/germ, factor, basepoint and dual-action proofs through AD and
  rewrites, and invalidate them after relevant function/model/domain/owner/version
  changes. A digest is a binding mechanism, not itself a correctness proof.
- Test tampered Core, swapped proof subjects, stale identities, wrong factor
  basepoints, dropped domain obligations and selected-to-true retagging through
  the actual public check/build path once the feature exists.
- Keep native realization, floating error contracts and ownership/resource
  safety separately established. Exact reference equality is not native refinement.

This adds a narrowly scoped instance of CS-established derivative premises and
CF correspondence. It does not discharge the general CF theorem, identify
analytic Fréchet derivatives with the existing algebraic/Kähler family without
its own bridge, or expand into general differentiability inference or metric work.
