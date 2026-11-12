# Historical Stages 2–7

This chapter is the roadmap of the language after its first executable core,
the finite Stage 1. It has six Stages and keeps their historical numbers. Each
Stage states a mathematical target and an acceptance example, an example that
could establish the completion of the Stage. Stages 2 and 3 are Implemented as
finite profiles over the rational numbers: each has a Status paragraph, a
Reference chapter and a [delivery record](../appendix/history.md). Stages 4
to 7 are Planned.

The Stages answer a sequence of mathematical questions. What structure does a
point see? How does a differential travel back along a map? Which quantities
survive a change of coordinates, an eigenvalue collision, or a change of
physical convention?

The GitHub issues that the chapter links govern the plan, including changes to
earlier proposals. Their states were checked on 12 November 2026 (JST). The
Status paragraphs of Stages 2 and 3 describe the delivered profiles, and the
opening of Stage 3 gives the declaration forms of its profile. Every other
implementation claim refers to the finite Stage 1 delivery at `7d612a4`.
[Stage 1 acceptance map](https://github.com/MGYamada/Vastitas/blob/7d612a4b76ef54a17bd859c466fb3407912ac14b/docs/stage1-acceptance.md)

Where the chapter says "the retired draft", it means the design draft v0.3 of
26 October 2026. The repository retired it on 4 November 2026, and Git keeps
it at `cc4922f`.

## Stage 2. Ordinary affine geometry

Stage 1 already distinguishes the objects supplied by
`std::geometry::scheme` and `std::geometry::smooth`. A point carries its
target and test object. Stage 2 gives the ordinary affine fragment coordinate
rings, polynomial maps, module presentations and fiber products over a
specified base. A ring homomorphism from A to B induces a scheme morphism
from Spec(B) to Spec(A), including its action on the structure sheaves.
[Spectrum correspondence, #362](https://github.com/MGYamada/Vastitas/issues/362)

**Acceptance example.** Over a field K, the ring K[ε]/(ε²) contains a
nonzero element whose square is zero. Its spectrum D has the same underlying
point set as Spec(K), yet the D-valued point of the affine line that sends
its coordinate to ε carries first-order information. Preserve ε through the
construction. For base change, recover Spec(A ⊗<sub>R</sub> B) from the two
specified maps to Spec(R). The three-index `MorphismOver(X,Y,S)` that #385
specifies records the structure maps and their commuting triangle separately
from the two-index, same-base `Morphism`. The delivered profile declares such
a morphism at a `relative` family of three indices, as
[Morphisms over a base](../affine-geometry.md#morphisms-over-a-base)
specifies. A Cartesian square needs the corresponding universal property. Reject a candidate square over a different base.
[Relative morphisms and base change, #385](https://github.com/MGYamada/Vastitas/issues/385)

**Status.** A finite, checked profile over QQ implements these examples
([guide](affine-geometry.md), [Reference](../affine-geometry.md),
[acceptance map](../stage2-acceptance.md), closed tracker #571). It has
presented objects and morphisms over a base with their triangles. It has fiber
products with Cartesian evidence, and principal opens with the action on the
structure sheaf. The acceptance example runs natively. The mathlib bridge
proves Buchberger's criterion and connects the accepted data to
`MvPolynomial`, `Spec.map`, `IsPullback` and `Localization.Away`. Planned, in
open issues: module presentations (#259, #261), the algebraic Kähler
differentials Ω (#688), ZZ and F_p coefficients (#251–#253), and gluing (#104,
#151).

## Stage 3. Smooth affine geometry and reverse AD

The retired draft uses `Affine(CInfReal, n)` in examples. In function bodies that
spelling keeps its Stage 1 meaning, a descriptor of the smooth setting, and
the Stage 1 compatibility adapter continues to resolve its historical inputs.
Smooth real affine space is declared as `Affine(n)[c₁, …, cₙ]`, and ordinary
affine space over an explicit algebraic base as `Affine(K, n)[…]`. ADR 0001
decides that a smooth manifold is a `CInfScheme` with checked local and
topological evidence and has no type of its own; that evidence and gluing are
Planned (#606). [Affine constructors, #103](https://github.com/MGYamada/Vastitas/issues/103) · [Geometric refinements, closed #360](https://github.com/MGYamada/Vastitas/issues/360) · [Implemented geometry migration](../internals/indexed-checker.md#finite-geometry-migration-acceptance)

**Acceptance example.** Given smooth maps f and g, start with a covector at
g(f(x)). Pull it back first along g at f(x), then along f at x. Check that
the result agrees with the pullback along the composite and belongs to the
cotangent space at x. A seed from a different point must fail. The mathematical
operation belongs to `std::differential`. A reverse pass for admitted smooth
primitives must agree with it on the checked program, including any
saved or recomputed forward values. Where the retired draft writes
`grad(loss)`, a
gradient is an ordinary function that applies a declared `sharp` to the
differential. `sharp` names a metric and evidence of its nondegeneracy, even
in Euclidean coordinates. The comparison with analytic Fréchet
derivatives and the comparison with polynomial Kähler differentials are
distinct proof obligations. [Cotangent semantics, #381](https://github.com/MGYamada/Vastitas/issues/381) · [Compiled pullbacks, #361](https://github.com/MGYamada/Vastitas/issues/361) · [Explicit metric operations, #264](https://github.com/MGYamada/Vastitas/issues/264)

**Status.** A finite, checked profile over QQ implements this example
([guide](smooth-geometry.md), [Reference](../language/smooth-declarations.md),
[acceptance map](../stage3-acceptance.md), closed tracker #604). It has smooth
affine objects and exact polynomial maps, and covectors and vectors at
rational points. Its reverse pass runs with saved or recomputed forward
values over the program that checked Core builds. Its metrics are named and
constant, with checked nondegeneracy and Riemannian evidence. The acceptance
example runs natively. The oracle proves
the chain rule without mathlib, and the mathlib bridge proves the Fréchet and
Kähler comparisons as separate theorems. The kernel compiles each reverse
pass that it can read into Core and checks that Core again. The oracle and
the bridge prove what each generated function computes. The oracle also
proves what each compiled site computes, under premises that no theorem
discharges (#665). The compiled-entry theorems keep premises of their own
(#668). Whole modules agree with their source in tests, and the theorem of
their refinement is Planned (#665;
[compiled reverse Core acceptance](../reverse-core-acceptance.md), closed
tracker #623). Planned, in open issues: forward execution by a third party
(#161), the semantics of Hessian-vector products (#381), custom rules (#163),
gluing (#606), position-dependent metrics (#264), a `gradient` that the
standard library exports (#626) and performance (#222).
Compiled reverse Core keeps its residuals as immutable pure Core values,
retained or recomputed, as
[storage ownership §7.10](../storage-ownership.md#residual-retention)
records. Storage-backed residual retention, with its value versions and
invalidation, remains open. The tape of this profile is an immutable runtime
value that records none of that metadata.

## Stage 4. Bundles and tensor diagrams

Stage 1 checks nominal bases, explicit dual and conjugate operations, storage
loans and the single use of each contraction port in its finite numerical
profiles. The next mathematical targets include finite locally free module
sheaves, Grassmannians classifying subbundles, and tensor diagrams with
dimension grades. For the common `⊗`, the current plan selects one certified
monoidal model and its owned implementation. Ordinary and graded models may
share a carrier. If implicit selection is ambiguous, the caller must select
a model explicitly to determine the laws and signs. [Bundles, #261](https://github.com/MGYamada/Vastitas/issues/261) · [Tensor coherence, #201](https://github.com/MGYamada/Vastitas/issues/201) · [Model selection, #387](https://github.com/MGYamada/Vastitas/issues/387)

**Acceptance example.** Lower one accepted linear map in two different valid,
nonorthogonal ordered bases. The arrays may differ. Decoding either array
must recover the same map between the same spaces. For point-dependent
frames, retain the basepoint and fiber as well. Contraction must preserve the
endpoints and the caller's ownership of buffers. On a chart with a length
coordinate x and a time coordinate t, reject dx² + dt². A declared metric
using compatible scales can make the sum meaningful. Issue #518 adapts
basis-adequacy arguments from the *Grassmann* language, starting with finite
real inner-product spaces and selected positive metrics. It calls for a proof
about the same accepted Vastitas Core in both bases. An optimized change of
representation also needs a validated lowering, including its floating-point
and ownership obligations. [Basis adequacy, #518](https://github.com/MGYamada/Vastitas/issues/518) · [Metric operations, #264](https://github.com/MGYamada/Vastitas/issues/264)

## Stage 5. Spectral observations

The retired draft's lazy eigenvalue and SVD descriptions allow a program to request
an invariant or an externally separated Hermitian cluster. For an exact
finite endomorphism H, the current spectral plan retains both its
characteristic scheme and the module on which the coordinate acts as H.
A scalar matrix and a nontrivial Jordan block can have the same characteristic
polynomial and different module actions. A numerical adapter must identify
the observation it computes. [Exact spectral pair, #337](https://github.com/MGYamada/Vastitas/issues/337)

**Acceptance example.** For the symmetric matrix with rows (x, y) and
(y, −x), the eigenvalues ±√(x² + y²) meet at the origin. The invariant
tr(H²) = 2(x² + y²) has gradient (4x, 4y) everywhere for the declared
dimensionless Euclidean chart. A cluster derivative additionally needs a
gap to the rest of the spectrum. A merged Lean bridge already proves a
finite-spectrum derivative of functional calculus on self-adjoint inputs,
including repeated eigenvalues. Its codomain is the ambient algebra. The
typed Hermitian lift, cotangent action and agreement with emitted reverse
Core remain open. [Proved Daleckii–Krein statement](https://github.com/MGYamada/Vastitas/blob/7d612a4b76ef54a17bd859c466fb3407912ac14b/docs/daleckii-krein.md) · [Spectral AD obligations, #471](https://github.com/MGYamada/Vastitas/issues/471)

## Stage 6. A first physical model

Follow a single finite model from assumptions to a comparison with data.
For a two-level Hamiltonian, declare what the parameters mean, their units,
the state preparation, the observable and the regime in which the model is
intended to apply. The current library plan assigns pure mathematics to
`std`, explicit computational policies and effects to `monad`, and physical
interpretation, conventions and uncertainty to `nature`. [Library responsibilities, #304](https://github.com/MGYamada/Vastitas/issues/304) · [Physics conventions, #374](https://github.com/MGYamada/Vastitas/issues/374)

**Acceptance example.** Record the model's exact prediction, the result
obtained under a named solver and approximation policy, and a comparison
against a calibrated dataset with stated uncertainty. Change the calibration.
The comparison depending on it becomes stale. A mathematical derivation whose
assumptions are unchanged can still be checked. The numerical error bound
and physical measurement uncertainty each need their own evidence.
[Uncertainty and provenance, #299](https://github.com/MGYamada/Vastitas/issues/299)

## Stage 7. Broader geometry and physics

The historical stage groups gluing, additional monoidal structures and
domain libraries. The current issues specify individual constructions and
their prerequisites. For gluing, choose the site, certify a cover, and check
that local data agree on overlaps. General site machinery and the
geometry-specific choice of smooth or Zariski opens have separate owners.
[Verified covers, #98](https://github.com/MGYamada/Vastitas/issues/98) · [Gluing-first geometry, closed #360](https://github.com/MGYamada/Vastitas/issues/360)

**Acceptance example.** Glue two algebraic affine lines along their
punctured Zariski opens by y = 1/x and exhibit an isomorphism with the
projective line over K. For the smooth-real construction, gluing the
corresponding smooth opens gives a `CInfScheme`. Identifying the real
projective line as a smooth manifold requires additional evidence. Swapping
the sites or using a map without a certified inverse must fail. A further
physics library would also have to specify the numerical realization and the
physical meaning of any reported observation. [Algebraic projective line, #104](https://github.com/MGYamada/Vastitas/issues/104) · [Smooth gluing and the real projective line, #606](https://github.com/MGYamada/Vastitas/issues/606)

## Release gates and performance

Historical stage numbers describe research goals. The release issues name
work that a version must ship. Each version has a label, and the lists below
name every open issue that carried the label on 12 November 2026.

- **v0.1.0**, with the label `0.1.0 TODO`, calls for one static family per named `fn`. Its planned production
  path runs from accepted Lean Core through a single MidIR with optimization
  and execution phases to the exact LLVM IR bytes passed to the native backend.
  The default Fast mode audits evidence bound to those artifacts with the
  nanoda checker shipped with the pinned Lean toolchain.
  Official mode and release proof claims require the pinned official Lean
  kernel. [Function families, #462](https://github.com/MGYamada/Vastitas/issues/462) · [LLVM gate, #417](https://github.com/MGYamada/Vastitas/issues/417) · [Verification modes, #282](https://github.com/MGYamada/Vastitas/issues/282)
  The label also carries these issues:
  - structured `assemble` blocks for each function family, in place of the
    flat `assembly` trace (#455);
  - turbofish-first numerical realizations of RR and CC in F32 and F64, with
    `Affine` wrappers (#686);
  - the freeze of the semantic aliases `Vector`, `Matrix` and `Tensor`, and
    monad-backed numerical execution (#689);
  - `monad::float` for the explicit numerical interpretation of RR and CC
    (#318);
  - a policy for retiring superseded wire protocol versions and their
    decoders (#533);
  - `std::category` (#199) and `monad::kleisli` (#206).
- **v0.2.0**, with the label `0.2.0 TODO`, requires a Lean-native production frontend and CLI, authenticated
  reuse of compiled objects, and the finite container, named algorithm and
  string interfaces implemented in ordinary `.vast`. [Frontend, #152](https://github.com/MGYamada/Vastitas/issues/152) · [Cache, #339](https://github.com/MGYamada/Vastitas/issues/339) · [Standard library, #388](https://github.com/MGYamada/Vastitas/issues/388)
  The label also carries these issues:
  - the Core implementation of generic memory, algebraic data types and
    iteration (#405), and the Core design issues #407 to #413;
  - the freeze of the Rust-style surface language and of `edition = "2026"`
    (#458);
  - deterministic LLVM code-generation units with an authenticated object
    cache for each unit (#487).
- **v0.3.0 through v1.0.0** spans the proposed constitutional theorem
  statements and their eventual kernel-checked proofs for the declared
  certified scope. The basis work can enter a release only through an
  explicitly admitted fragment. [Constitutional plan, #192](https://github.com/MGYamada/Vastitas/issues/192) · [Theorem transfer, #518](https://github.com/MGYamada/Vastitas/issues/518)
  - The label `0.3.0 TODO` carries #192 and these issues: the flagship gate
    from certified tensors through scheme morphisms to geometric automatic
    differentiation (#688), lazy generics with partial JIT (#596), the
    admission of semantic generics (#642) and the proposal of a constitutional
    governance framework (#693).
  - The label `1.0.0 TODO` carries proof-driven development (#472), the proof
    harness (#474) and the thinking compiler with its trace, diagnostics,
    security charter, bot and dialectic (#488, #489, #493, #494, #496, #498).

**Fast like C** is the primary performance goal: the C/C++-class target of
the language.
Stage 1 closed with its finite safety and execution evidence and its known
performance differences. Stages 2 and 3 closed without a performance claim.
The acceptance of the target is Planned (#222): the controlled Linux
comparison with equivalent standalone C, the absolute tiny-call overhead
budget set before acceptance, and the remaining Lean, allocator and OpenBLAS
cost attribution.
[Performance evidence and acceptance](../storage-ownership.md#performance-evidence-and-acceptance)
states the conditions of that comparison. Preserve
both full-lifecycle and prepared/reuse measurements with matching algorithms,
layouts, scalar types, thread counts and output contracts. Shared-host
observations retain their original comparator and uncertainty.
[Delivery decision, #179](https://github.com/MGYamada/Vastitas/issues/179#issuecomment-6602653283) · [Cost attribution, #183](https://github.com/MGYamada/Vastitas/issues/183#issuecomment-6602672759) · [Performance acceptance, #222](https://github.com/MGYamada/Vastitas/issues/222#issuecomment-6602667492)
