# Appendix C: Reference models

A **reference model** is an independent Python program under
[`scripts/`](https://github.com/MGYamada/Vastitas/tree/main/scripts) with its
own regression tests. It studies a construct or a certificate format that a
GitHub issue proposes, on small inputs and with exact arithmetic. The model
fixes the mathematical meaning of the construct, the evidence that a checker
must verify and the inputs that it must reject.

A reference model is not a part of the compiler. The compiler does not run
it, and no accepted program depends on it. A result of a model is not Vastitas
execution, compiler acceptance, an entry of the standard library or a Lean
proof. The construct that a model studies is Planned, unless
[the table below](#the-models-and-the-compiler) says that the compiler
implements a part of it.

Each chapter has one section for each model. The section gives the commands
that run the model and its tests, its scope, the inputs that it trusts and the
obligations that remain before a connection to the compiler. A section keeps
the record of the change that added its model. Its statements about the
compiler, the continuous integration and the issues describe the repository at
that change, and many sections name the revision that they inspected. The
opening table of each chapter states what the compiler implements today.

The tests of every model run in the continuous integration, in the step
`python3 -m unittest discover -s scripts -p 'test_*.py'`. They need Python 3.10
or later and its standard library. One test of the diagnostics model runs
the built compiler, and the step skips it where the compiler is not built; the
native compiler jobs run it after their build.

## The models and the compiler

| Chapter | Models | In the compiler |
| --- | --- | --- |
| [Diagnostics, doctests and identifiers](../reference/compiler-tools.md) | [Non-punitive diagnostics](../reference/compiler-tools.md#diagnostic-reference) · [Expected-rejection doctest results](../reference/compiler-tools.md#doctest-result-reference) · [Identifier ASCII round-trip](../reference/compiler-tools.md#identifier-ascii-reference) | Implemented: [diagnostics](../language/diagnostics.md) with a code, a message, a place and notes, and ASCII [identifiers](../language/lexical-structure.md#identifiers). The records of the three models are models only |
| [Analysis, certificates and random supplies](../reference/analysis-and-effects.md) | [ℓ² tail certificates](../reference/analysis-and-effects.md#l2-tail-reference) · [Polynomial integral enclosures](../reference/analysis-and-effects.md#integral-reference) · [SOS covers](../reference/analysis-and-effects.md#sos-reference) · [Random supplies](../reference/analysis-and-effects.md#rand-reference) · [Derivative-rule coherence](../reference/analysis-and-effects.md#derivative-coherence-reference) | Implemented: reverse pullbacks of polynomial [smooth maps](../language/smooth-declarations.md#reverse-pass-primitives). The five models are models only |
| [Exact geometry reference models](../reference/geometry.md) | [Real-plane metrics](../reference/geometry.md#metric-reference) · [Polynomial symplectic maps](../reference/geometry.md#symplectic-reference) · [First variations](../reference/geometry.md#variational-reference) · [Finite Čech covers](../reference/geometry.md#cech-reference) · [SSH Bloch and Fermi schemes](../reference/geometry.md#ssh-toric-reference) · [Elliptic addition](../reference/geometry.md#elliptic-reference) · [Pointwise Hodge star](../reference/geometry.md#hodge-reference) | Implemented: constant [metrics](../language/smooth-declarations.md#metrics) with `flat` and `sharp` on smooth affine objects, and [presented affine geometry](../affine-geometry.md) over the rational numbers. The other six models are models only |
| [Algebra, order and symmetry reference models](../reference/algebra-and-symmetry.md) | [CAR and ordinary spin](../reference/algebra-and-symmetry.md#car-spin-reference) · [Orders, lattices and Galois connections](../reference/algebra-and-symmetry.md#order-reference) · [Time reversal](../reference/algebra-and-symmetry.md#time-reversal-reference) · [Finite spectral pairs](../reference/algebra-and-symmetry.md#finite-spectral-reference) | The four models are models only |
| [Execution and planning reference models](../reference/execution-plans.md) | [CUDA storage reuse](../reference/execution-plans.md#cuda-reuse-reference) · [CSR patterns and SpGEMM](../reference/execution-plans.md#sparse-reference) · [Reduction plans](../reference/execution-plans.md#reduction-reference) · [Float and SafeFloat](../reference/execution-plans.md#float-reference) · [Dependency invalidation](../reference/execution-plans.md#incremental-reference) | Implemented: [storage](../storage-ownership.md) on the host and dense [numerical maps](../linalg/maps-and-gemm.md). The five models are models only |

## Models described in other chapters

Four other reference models are described next to the compiler component
that they model:

- the model of the
  [graph crossing checker](../verification/core-models.md#graph-crossings),
  `scripts/graph_reference.py`;
- the
  [dense layout and preflight reference](../storage/checked-storage.md#storage-layout-preflight),
  `scripts/storage_layout_reference.py`;
- the model of exact polynomial algebra, `scripts/affine_algebra_reference.py`.
  A kernel regression compares the kernel's Gröbner bases and normal forms
  with a fixture that the model keeps, as
  [Verification boundaries](../verification.md) records;
- `scripts/smooth_differential_reference.py`, which writes a fixture from the
  two models of [real-plane metrics](../reference/geometry.md#metric-reference).
  A kernel regression compares the smooth runtime of the kernel with that
  fixture, as the [Stage 3 acceptance record](../stage3-acceptance.md#c16)
  states.
