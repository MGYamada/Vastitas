# Hilbert spaces from Cauchy completion — mathematical and constructive profiles

**Status:** design and future proof obligations only. This document does not claim an implemented `.vast` interface, a finished Lean theorem, automatic analytic decision procedures, or numerical algorithms.

**Owners:** [#382](https://github.com/MGYamada/Vastitas/issues/382) (general uniform/metric completion), [#208](https://github.com/MGYamada/Vastitas/issues/208) (pre-Hilbert → Hilbert and ℓ² specialization), [#209](https://github.com/MGYamada/Vastitas/issues/209) (Hilbert proof-obligation profile), [#367](https://github.com/MGYamada/Vastitas/issues/367) (filter convergence), [#190](https://github.com/MGYamada/Vastitas/issues/190)/[#191](https://github.com/MGYamada/Vastitas/issues/191) (optional executable lazy streams and finite-prefix memory safety), [#262](https://github.com/MGYamada/Vastitas/issues/262) (bounded and domain-bearing operators).

## Decision

`std::analysis::hilbert` is **Cauchy-completion first**. An abstract exact real/complex Hilbert space is an inner-product space whose induced normed uniform space is complete. A selected pre-Hilbert space `D` may be completed as `H = Completion(D)`. Countable `ℓ²`, orthonormal bases, finite coefficient arrays, tail-majorant rules and `InfList` are useful *presentations*, not prerequisites for the abstract Hilbert type.

The general completion construction is owned once by `std::topology::uniform`. It must retain its chosen uniformity, separatedness/quotient relation, dense embedding and universal property. **Arbitrary uniform spaces cannot be assumed to admit a sequence-only completion**; Cauchy filters/nets are the generic mathematical route. Normed and pre-Hilbert spaces are metric, so the Cauchy-sequence presentation applies there. Inner-product extension is the specialized responsibility of `std::analysis::hilbert`.

## The exact mathematical object

For exact `K = ℝ` or `ℂ`, choose a pre-Hilbert space `D` with a positive-definite inner product. In the complex case, follow pinned mathlib's convention: conjugate-linear in the **first** argument, linear in the **second**. Form the normed completion

$$
H = \widehat D,\qquad
\eta:D\longrightarrow H.
$$

The embedding `η` is dense and isometric; `H` is complete. The inner product extends uniquely and continuously from `D × D` to `H × H`, respecting the selected exact scalar structure and Hermitian laws. These properties are **Lean theorem obligations**, not the result of inspecting finitely many approximants.

In a metric presentation, two Cauchy sequences represent the same point exactly when

$$
(a_n)\sim(b_n)
\quad\Longleftrightarrow\quad
\lim_{n\to\infty}\|a_n-b_n\|=0.
$$

Name equality, literal sequence equality and Hilbert-element equality are distinct notions. A mathematical Hilbert element need not have a computable name. No arbitrary countable orthonormal basis, separability or global decidable equality is assumed.

## Constructive names: optional, exact and proof-carrying

A computable presentation additionally selects an **effectively represented dense fragment** `D₀`, a precise embedding `D₀ → D` and a supported exact scalar/metric profile (e.g. rational or Gaussian-rational finite-support vectors). It does not expose arbitrary abstract `ℝ`/`ℂ` coefficients as machine oracles.

A constructive name consists of finite/evaluable approximations `q(n) ∈ D₀` and an authenticated effective Cauchy modulus. A convenient *fast-name normal form* is

$$
\forall n\in\mathbb N,\quad
\|q(n+1)-q(n)\|\le 2^{-(n+1)}.
$$

Using completeness and the triangle inequality, this guarantees an exact element `x` with

$$
x=\lim_{n\to\infty}\eta(q(n)),\qquad
\|x-\eta(q(n))\|\le
\sum_{k=n}^{\infty}2^{-(k+1)}
=2^{-n}.
$$

A general supplied effective modulus may be accepted without forcing this normal form, provided its proof is checked; reindexing into a fast name is itself an explicit, justified computation. Names with the same limit are interchangeable only through a proved completion-equivalence witness. Checking a finite prefix, exact finite arithmetic on some samples, or productive runtime iteration is insufficient.

A certified `approx(name,n)` query provides a **stated error upper bound** for a finite realization, while `x` remains its exact mathematical limit. User-requested precision and certified approximation do not change exact `norm`, `inner` or semantic equality. An unknown effective name leads to `unsupported`, never a fabricated exact result.

## Lifting operations

Addition and scalar multiplication are continuous in the Hilbert norm, so their exact operations descend to completion elements. Their executable names may require a new index schedule or scalar magnitude bound.

For approximate names `x_n, y_n` with `‖x-x_n‖ ≤ δ_x` and `‖y-y_n‖ ≤ δ_y`, continuity yields a certified inner-product error:

$$
|\langle x,y\rangle-\langle x_n,y_n\rangle|
\le
\delta_x(\|y_n\|+\delta_y)+\|x_n\|\delta_y.
$$

Thus the exact extended inner product is independent of the names, and an executable approximation needs explicit norm/error evidence.

A **bounded** linear map `T:H→K` with proved operator bound `C` transports an approximation by

$$
\|Tx-Tx_n\|\le C\|x-x_n\|.
$$

An arbitrary linear map, an unbounded Hamiltonian, its domain membership, an adjoint or a graph-norm claim does **not** follow from this estimate. Those require [#262](https://github.com/MGYamada/Vastitas/issues/262)'s separate domain-aware mathematics.

## ℓ² and L² are derived cases

- **Sequence Hilbert spaces.** For a selected index type `I` and exact `K`, the usual function-with-square-summability model `ℓ²(I,K)` is isometric to the completion of finitely supported functions `c₀₀(I,K)`. That is an explicit mathematical equivalence theorem, not a requirement to use infinite streams. Effective names require an effective index/scalar presentation; countability is not a prerequisite for the abstract model.
- **Specialized coefficient certificates.** With a selected countable basis, finite partial sums and a checked tail bound give a Cauchy name. The existing [exact ℓ² tail reference](l2-tail-reference.md) verifies closed rational geometric/reciprocal schemas only; it is not a general completion checker and does not prove completeness. Computable coefficients plus mere square summability do **not** imply a computable norm-tail modulus.
- **`InfList`.** A productive, safe stream may produce coefficients or approximants. It is **not** required by `Hilbert`, and stream productivity/Ownership-Borrow correctness imply neither Cauchy convergence nor quotient-equality evidence.
- **`L²(X,μ)`.** This uses equality modulo μ-almost-everywhere equivalence, not raw pointwise-function identity. Constructive dense/simple-function presentations require their measure/integration hypotheses. A completion name does not authorize abstract point evaluation.

### A fully finite-support example

In `ℓ²(ℕ,ℂ)`, let `e_k` be the standard orthonormal basis and choose

$$
q_n = \sum_{k=0}^{n}2^{-k}e_k.
$$

Then `q_n` has Gaussian-rational finite-support coefficients and

$$
\|q_{n+1}-q_n\|=2^{-(n+1)},\qquad
x=\sum_{k\ge 0}2^{-k}e_k,\qquad
\|x\|^2=\frac43.
$$

The fast-name theorem yields `‖x-q_n‖≤2⁻ⁿ`. In fact, this particular orthogonal expansion has the sharper residual `‖x-q_n‖=2⁻ⁿ/√3`. The example shows how exact infinite-dimensional values can arise from finite calculations plus a proof without identifying `Hilbert` with `InfList`.

## Verification obligations and non-goals

Future acceptance must establish:

1. A selected completion embedding, quotient equivalence, generic Cauchy completeness and the inner-product extension against the exact mathematical semantics.
2. Dense finite approximants, effective modulus, residual bound, matching scalar/metric identities, and evidence attached to the **actual returned Core/environment** (#184/#209/#285).
3. Correct propagation through arithmetic, inner products and globally bounded operators; explicit failure for missing/forged/stale modulus, mismatched model, unjustified operator domain, or merely productive stream.
4. The isometric equivalence `Completion(c₀₀(I,K)) ≃ ℓ²(I,K)` under stated hypotheses, plus distinct `L²` a.e. quotient semantics.
5. Separate provenance for mathematical specification, reference Python regressions, executable profile, Lean-kernel proof and native/numerical refinement.

No ninth Domain Checker, no user-facing `unsafe` escape, no universal equality/convergence decision procedure, no implicit truncation tolerance, no compulsory `InfList` or orthonormal basis, and no release deadline. Existing exact ℓ² tail-reference tests remain valid **only** as a specialized profile, not as proof of this general design.