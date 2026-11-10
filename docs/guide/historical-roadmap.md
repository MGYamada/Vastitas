# Historical Stages 2–7

The historical roadmap has six stages after the first executable core. They answer a sequence of mathematical questions. What structure does a
point see? How does a differential travel back along a map? Which quantities
survive a change of coordinates, an eigenvalue collision, or a change of
physical convention?

This chapter keeps the historical stage numbers. Current GitHub issue
decisions govern the plan, including changes to earlier proposals. The examples
below are mathematical targets. Implementation claims refer to the finite
Stage 1 delivery at `7d612a4`. Issue decisions were checked on 4 November
2026 (JST). [Stage 1 acceptance map](https://github.com/MGYamada/Vastitas/blob/7d612a4b76ef54a17bd859c466fb3407912ac14b/docs/stage1-acceptance.md)

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
specified maps to Spec(R). The proposed `MorphismOver(X,Y,S)` records the
structure maps and their commuting triangle separately from the existing
two-index, same-base `Morphism`. A Cartesian square needs the corresponding
universal property. Reject a candidate square over a different base.
[Relative morphisms and base change, #385](https://github.com/MGYamada/Vastitas/issues/385)

**Status.** A finite, checked profile over QQ implements these examples:
presented objects, morphisms over a base with their triangles, fiber products
with Cartesian evidence, and principal opens with the action on the structure
sheaf ([chapter](../affine-geometry.md),
[acceptance map](../stage2-acceptance.md), tracker #571). The acceptance example
runs natively. The mathlib bridge proves Buchberger's criterion and connects the
accepted data to `MvPolynomial`, `Spec.map`, `IsPullback` and
`Localization.Away`. Module presentations (#259, #261), Ω (#381), ZZ and F_p
coefficients (#251–#253), and gluing (#104, #151) remain open.

## Stage 3. Smooth affine geometry and reverse AD

The draft uses `Affine(CInfReal, n)` in examples. In function bodies that
spelling keeps its Stage 1 meaning, a descriptor of the smooth setting, and
the Stage 1 compatibility adapter continues to resolve its historical inputs.
Smooth real affine space is declared as `Affine(n)[c₁, …, cₙ]`, and ordinary
affine space over an explicit algebraic base as `Affine(K, n)[…]`. ADR 0001
decides that a smooth manifold is a `CInfScheme` with checked local and
topological evidence and has no type of its own; that evidence and gluing are
planned. [Affine constructors, #103](https://github.com/MGYamada/Vastitas/issues/103) · [Geometric refinements, #360](https://github.com/MGYamada/Vastitas/issues/360) · [Implemented geometry migration](../internals/indexed-checker.md#geometry-migration)

**Acceptance example.** Given smooth maps f and g, start with a covector at
g(f(x)). Pull it back first along g at f(x), then along f at x. Check that
the result agrees with the pullback along the composite and belongs to the
cotangent space at x. A seed from a different point must fail. The mathematical
operation belongs to `std::differential`. A reverse pass for admitted smooth
primitives must agree with it on the actual checked program, including any
saved or recomputed forward values. Where the draft writes `grad(loss)`, a
gradient is an ordinary function that applies a declared `sharp` to the
differential. `sharp` names a metric and evidence of its nondegeneracy, even
in Euclidean coordinates. The comparison with analytic Fréchet
derivatives and the comparison with polynomial Kähler differentials are
distinct proof obligations. [Cotangent semantics, #381](https://github.com/MGYamada/Vastitas/issues/381) · [Compiled pullbacks, #361](https://github.com/MGYamada/Vastitas/issues/361) · [Explicit metric operations, #264](https://github.com/MGYamada/Vastitas/issues/264)

**Status.** A finite, checked profile over QQ implements this example
([reference](../language/smooth-declarations.md),
[acceptance map](../stage3-acceptance.md), tracker #604): smooth affine
objects and exact polynomial maps, covectors and vectors at rational points,
a reverse pass with saved or recomputed forward values over the program that
checked Core builds, and named constant metrics with checked nondegeneracy and
Riemannian evidence. The acceptance example runs natively. The oracle proves
the chain rule without mathlib, and the mathlib bridge proves the Fréchet and
Kähler comparisons as separate theorems. The kernel compiles each reverse
pass that it can read into Core and checks that Core again. The oracle and
the bridge prove what each generated function computes, and each compiled
site under premises that no theorem discharges yet; whole modules agree with
their source in tests (#665;
[compiled reverse Core acceptance](../reverse-core-acceptance.md), tracker
#623). Forward mode and Hessian-vector products (#161), custom rules (#163),
gluing (#606), position-dependent metrics and performance (#222) remain open.
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

The draft's lazy eigenvalue and SVD descriptions allow a program to request
an invariant or an externally separated Hermitian cluster. For an exact
finite endomorphism H, the current spectral plan retains **both** its
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
[Verified covers, #98](https://github.com/MGYamada/Vastitas/issues/98) · [Gluing-first geometry, #360](https://github.com/MGYamada/Vastitas/issues/360)

**Acceptance example.** Glue two algebraic affine lines along their
punctured Zariski opens by y = 1/x and exhibit an isomorphism with the
projective line over K. For the smooth-real construction, gluing the
corresponding smooth opens gives a `CInfScheme`. Identifying the real
projective line as a smooth manifold requires additional evidence. Swapping
the sites or using a map without a certified inverse must fail. A further
physics library would also have to specify the numerical realization and the
physical meaning of any reported observation. [Algebraic projective line, #104](https://github.com/MGYamada/Vastitas/issues/104) · [Smooth projective line, #103](https://github.com/MGYamada/Vastitas/issues/103)

## Release gates and performance

Historical stage numbers describe research goals. The following release
issues name work a version must ship.

- **v0.1.0** calls for one static family per named `fn`. Its planned production
  path runs from accepted Lean Core through a single MidIR with optimization
  and execution phases to the exact LLVM IR bytes passed to the native backend.
  The default Fast mode audits evidence bound to those artifacts with the
  nanoda checker shipped with the pinned Lean toolchain.
  Official mode and release proof claims require the pinned official Lean
  kernel. [Function families, #462](https://github.com/MGYamada/Vastitas/issues/462) · [LLVM gate, #417](https://github.com/MGYamada/Vastitas/issues/417) · [Verification modes, #282](https://github.com/MGYamada/Vastitas/issues/282)
- **v0.2.0** requires a Lean-native production frontend and CLI, authenticated
  reuse of compiled objects, and the finite container, named algorithm and
  string interfaces implemented in ordinary `.vast`. [Frontend, #152](https://github.com/MGYamada/Vastitas/issues/152) · [Cache, #339](https://github.com/MGYamada/Vastitas/issues/339) · [Standard library, #388](https://github.com/MGYamada/Vastitas/issues/388)
- **v0.3.0 through v1.0.0** spans the proposed constitutional theorem
  statements and their eventual kernel-checked proofs for the declared
  certified scope. The basis work can enter a release only through an
  explicitly admitted fragment. [Constitutional plan, #192](https://github.com/MGYamada/Vastitas/issues/192) · [Theorem transfer, #518](https://github.com/MGYamada/Vastitas/issues/518)

**Fast like C remains the primary performance goal.** Stage 1 closed with
its finite safety and execution evidence and its known performance differences.
Stage 2 or later owns the controlled Linux comparison with equivalent
standalone C, the absolute tiny-call overhead budget set before acceptance,
and the remaining Lean, allocator and OpenBLAS cost attribution. Preserve
both full-lifecycle and prepared/reuse measurements with matching algorithms,
layouts, scalar types, thread counts and output contracts. Shared-host
observations retain their original comparator and uncertainty.
[Delivery decision, #179](https://github.com/MGYamada/Vastitas/issues/179#issuecomment-6602653283) · [Cost attribution, #183](https://github.com/MGYamada/Vastitas/issues/183#issuecomment-6602672759) · [Performance acceptance, #222](https://github.com/MGYamada/Vastitas/issues/222#issuecomment-6602667492)
