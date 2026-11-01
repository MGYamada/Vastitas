# Exact real ℓ² tail-certificate reference

This document is a **specialized coefficient-tail example**, not the foundation
of the Hilbert API. The general design is [Cauchy completion of pre-Hilbert
spaces](hilbert-cauchy-completion.md): a checked dense-fragment Cauchy name and
its convergence modulus may represent Hilbert elements **without** an `InfList`,
countable orthonormal basis, or coefficient-tail schema. These two rational
rules remain useful for a selected `ℓ²` specialization. They do not prove the
general completion construction, a complete executable subspace, or name equality.

This scoped reference implements two executable certificate rules for
[#208](https://github.com/MGYamada/Vastitas/issues/208) and
[#209](https://github.com/MGYamada/Vastitas/issues/209). It is a Python development
reference, not a public `.vast` feature, a Lean-verified checker, or compiler
acceptance. Neither issue is completed by this increment.

## Representation and mathematical meaning

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

## Closed proof rules

For both rules the target is the stronger finite-interval inequality

$$
\forall N\le M,\quad
\sum_{n=N}^{M-1}|x_n|^2\le B(N)-B(M)\le B(N),
\qquad B(N)\ge0,\qquad B(N)\longrightarrow0.
$$

The following are mathematical derivations of the rule schemas. Their Lean
formalization and the soundness of the executable checker are **pending**.
Finite regression tests are not substitutes for these universal derivations.

### Geometric-square telescope

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
`unsupported` is deliberately not a proof of nonmembership.

### Reciprocal-square comparison

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

## Acceptance and evidence binding

[`l2_tail_reference.py`](../scripts/l2_tail_reference.py) checks the full
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

## Lean semantic propositions to establish

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

## Actual returned-Core integration obligation

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

## Reproduction and verification status

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

One deliberately understated geometric coefficient is `4/3 - 10^(-100)`.
Every sampled interval still obeys its weak finite bound, yet the exact rule
rejects it. Tests also disable the observation functions and candidate producer
while checking certificates. These regressions guard against sampling-based
acceptance; they do not establish universal analytic statements.

| Layer | Status in this increment |
| --- | --- |
| Closed rational rule checking and reference return/snapshot audit | Implemented; focused tests executed |
| Finite rational observations | Executed as regressions only |
| General analytic implication and two rule soundness propositions | Specified above; no new Lean proof or build |
| Actual compiler generator extraction, returned-Core/ledger composition | Pending; reference records are not compiler certificates |
| Ordinary compiler dependency isolation | No dependency/import changes; boundary checker executed; existing no-mathlib CI retained |
| ℓ² completeness, general inner products/operators, iterator memory safety | Outside this fragment; no guarantee added |

Existing CI already discovers `scripts/test_*.py`. Python remains development
infrastructure. Neither ordinary compilation nor generated programs invoke
this reference or mathlib. A future Lean implementation must keep executable
checks in the mathlib-free kernel and analysis proofs in the proof-only oracle;
it must compose the frozen 8+1 architecture rather than add another checker.
