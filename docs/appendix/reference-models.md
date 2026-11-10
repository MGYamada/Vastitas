# Appendix C: Reference models

The repository contains small, independent reference models, mostly in Python
under [`scripts/`](https://github.com/MGYamada/Vastitas/tree/main/scripts). Each
one studies a proposed feature or certificate format before it reaches the
compiler. Each model has its own regression tests.

A reference model is **not** Vastitas execution, compiler acceptance, a
production standard-library entry or a Lean proof. Each section states its exact
scope, its trusted inputs and the obligations that remain before any
connection to the compiler.

| Chapter | Models |
| --- | --- |
| [Diagnostics, doctests and identifiers](../reference/compiler-tools.md) | [Non-punitive diagnostics](../reference/compiler-tools.md#diagnostic-reference) · [Expected-rejection doctest results](../reference/compiler-tools.md#doctest-result-reference) · [Identifier ASCII round-trip](../reference/compiler-tools.md#identifier-ascii-reference) |
| [Analysis, certificates and random supplies](../reference/analysis-and-effects.md) | [ℓ² tail certificates](../reference/analysis-and-effects.md#l2-tail-reference) · [Polynomial integral enclosures](../reference/analysis-and-effects.md#integral-reference) · [SOS covers](../reference/analysis-and-effects.md#sos-reference) · [Random supplies](../reference/analysis-and-effects.md#rand-reference) · [Derivative-rule coherence](../reference/analysis-and-effects.md#derivative-coherence-reference) |
| [Exact geometry reference models](../reference/geometry.md) | [Real-plane metrics](../reference/geometry.md#metric-reference) · [Polynomial symplectic maps](../reference/geometry.md#symplectic-reference) · [First variations](../reference/geometry.md#variational-reference) · [Finite Čech covers](../reference/geometry.md#cech-reference) · [SSH Bloch and Fermi schemes](../reference/geometry.md#ssh-toric-reference) · [Elliptic addition](../reference/geometry.md#elliptic-reference) · [Pointwise Hodge star](../reference/geometry.md#hodge-reference) |
| [Algebra, order and symmetry reference models](../reference/algebra-and-symmetry.md) | [CAR and ordinary spin](../reference/algebra-and-symmetry.md#car-spin-reference) · [Orders, lattices and Galois connections](../reference/algebra-and-symmetry.md#order-reference) · [Time reversal](../reference/algebra-and-symmetry.md#time-reversal-reference) · [Finite spectral pairs](../reference/algebra-and-symmetry.md#finite-spectral-reference) |
| [Execution and planning reference models](../reference/execution-plans.md) | [CUDA storage reuse](../reference/execution-plans.md#cuda-reuse-reference) · [CSR patterns and SpGEMM](../reference/execution-plans.md#sparse-reference) · [Reduction plans](../reference/execution-plans.md#reduction-reference) · [Float and SafeFloat](../reference/execution-plans.md#float-reference) · [Dependency invalidation](../reference/execution-plans.md#incremental-reference) |

The [graph crossing checker](../verification/core-models.md#graph-crossings) and
the [dense layout/preflight reference](../storage/checked-storage.md#storage-layout-preflight)
are described next to the compiler components they model.
