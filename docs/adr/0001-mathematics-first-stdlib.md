# ADR 0001 — Mathematics-first standard-library admission and trust boundary

- **Status:** Proposed; normative if this ADR is merged
- **Date:** 2026-10-28
- **Scope:** Standard-library governance and mathematical contracts, **not** a claim of implemented or proved functionality
- **Decision issue:** [#107](https://github.com/MGYamada/Vastitas/issues/107)
- **Implementation tracker:** [#160](https://github.com/MGYamada/Vastitas/issues/160)
- **Dependency amendment proposal (2026-10-30):** §9, first migration increment of [#285](https://github.com/MGYamada/Vastitas/issues/285); effective upon review and merge of this amendment.

## Context and decision

Vastitas aims to make textbook mathematical objects directly usable in one language for Math 2.0 and Physics 2.0. This requires a substantial, coherent `std`, but does not imply that every useful numerical algorithm belongs there.

**The standard library admits foundational mathematical denotations and the contracts needed to manipulate them; it does not become a catalogue of competing approximation schemes.** The policy below governs new public mathematical operations and families. It freezes **admission rules**, not a closed list of all future standard-library families and not a release deadline.

The word `ε` in the exclusion rule means a numerical approximation tolerance, not a nilpotent element of a Weil algebra.

### 1. Three responsibility layers

1. **Core:** generic indexed types and identities, ownership/borrowing, function and method authority, dispatch/coherence, generic checked IR, typed evidence validation and structural compiler transformations. No growing set of special-case privileges keyed by the spelling of a mathematical type.
2. **Mathematical `std`:** ordinary versioned `.vast` definitions and contracts for mathematical structures, maps, invariants, equations and supported exact/reference operations. Where necessary it exposes checked interfaces for admitted primitive/derivative rules and realization boundaries. Abstract definitions may exist without a universal evaluator.
3. **Ecosystem and selectable backends:** algorithms that approximate or realize mathematical targets using mesh, time step, polynomial degree as a refinement parameter, sampling, cutoff, stopping criteria, tolerance, resource schedule or backend-specific numerical behavior. Examples include quadrature, ODE/PDE solvers, optimizers, sparse iterative eigensolvers, Monte Carlo, DMRG/VUMPS and high-performance kernels.

A Core mechanism may support a mathematical `std` contract without making its concrete mathematical operations compiler intrinsics. Importing a package must not silently expand edit authority, executable capabilities or the trusted proof boundary.

### 2. Normative admission test

A proposed `std` mathematical operation **MUST** document all of the following.

**A. Intrinsic, algorithm-independent denotation.** With explicit mathematical data and hypotheses—such as a coefficient domain, term order, topology, measure, operator domain, representation, metric, chosen branch or phase convention—the result is characterized independently of an implementation, up to a **declared equivalence or canonical form**. Two conforming exact implementations target that same result. Neither name equality nor matching storage shape establishes identity.

**B. Foundational target, not a selected approximation protocol.** The public operation specifies an object, map, invariant, equation or structurally canonical computation in the mathematical theory itself. Its meaning is **not** the output of one chosen iterative/discretization/sampling strategy for approximating a different target. A refinement count or stopping rule supplied to obtain an approximate answer remains a realization policy, even if that algorithm is deterministic and well defined.

**C. No hidden numerical choice in the mathematical result.** The denotation MUST NOT depend on a default approximation tolerance, mesh, sampling rule, truncation threshold, convergence check, numeric branch heuristic or secretly chosen solver. Resource exhaustion may produce a reported failure or unsupported result; it must not silently redefine success. Mathematical choices that truly change the object (e.g. a term order, measure or boundary condition) are explicit **semantic data**, not hidden numerical options.

**D. Law, domain, equivalence and evidence contract.** State algebraic/analytic hypotheses, relevant domains, regularity, object/basepoint identity, equality notion, admissible scalar/profile, error and failure behavior, and which obligations are checked, assumed or not supported. No general termination, existence, equality decision, numerical guarantee or formal theorem may be inferred from an abstract type name.

The test is **necessary but not an automatic theorem of admission**. A mathematical formula can define an unbounded number of distinct algorithms. A proposal must justify that its public operation is foundational rather than simply one selectable method in an approximation family. Admission decisions, including exclusions, are made explicitly and versioned through the procedure below.

### 3. Deliberate positive and negative boundary examples

| Mathematical target in `std` | Permitted implementation / external realization | Deliberate exclusion from the `std` semantic API |
| --- | --- | --- |
| Reduced Gröbner basis over an admitted **exact field**, with fixed monomial order | Buchberger or F4 and independently checked certificates | An `ExactField` instance for a machine float, or unspecified term order |
| Typed finite composition/contraction | Dense, sparse, GEMM/BLAS kernels with explicit numerical policies | One mandatory BLAS implementation or exact-equality claims from floating output |
| Abstract Lebesgue integral for an explicit measure | External quadrature/cubature | Implicit `integrate` using a hidden step/tolerance |
| Typed ODE/PDE equation and its mathematically specified solution object/space | External Runge–Kutta, FEM and other solver packages | A built-in default time step, mesh, adaptive convergence policy |
| `eigen(H) = (Σ_H, ℱ_H)` for an admitted finite endomorphism | Optional numerical LAPACK observations with basis/error provenance | Implicit numerical diagonalization or canonical eigenvectors at degeneracy |
| Spectral measure of an admitted infinite-dimensional self-adjoint operator | Explicit numerical approximation of projections/spectral integrals | Automatic discrete eigenbasis for continuous spectrum |
| Equivariant `Hom_G(V,W)` and typed tensor meaning | Optional block-sparse and fusion-tree representation | DMRG or symmetric-TN optimization as mandatory std algorithms |

**Why the quadrature boundary needs both A and B:** a fixed Gauss–Legendre rule `Q_n` is a perfectly precise mathematical functional and exact on its specified polynomial subspace. That fact alone does not make the *selection of `Q_n` to approximate an integral* a foundational `std` evaluator. Its `n` is a method/refinement decision for an independently specified integral, not an intrinsic requirement of the input measure/function. Orthogonal-polynomial structures may be mathematical objects in `std`; a quadrature package remains an optional consumer of them.

For finite spectral semantics, `eigen(H)` is the spectral scheme together with its module, retaining multiplicity/Jordan information. A dense eigensolver may implement an observation backend; its eigenvector ordering, gauge, degeneracy handling and numerical errors are not intrinsic. The infinite-dimensional spectral theorem has the distinct projection-valued-measure contract.

An algorithm-free abstract definition may be admitted as **specified but not executable**. The absence of a universal solution procedure for infinite-dimensional Hilbert spaces, general schemes, or nonlinear PDEs is not a reason to expel their mathematical vocabulary from `std`.

### 4. Mathematical family boundaries

The initial *responsibility spine* consists of:

- `std::algebra::{group,ring,field,representation}`: groups/actions/homomorphisms; rings/modules/ideals/quotients; fields/extensions/finite Galois structures; representations, characters, tensor multiplicities and `Hom_G`. Exact executable profiles and hypotheses are explicit. For `Rep(SU(2))`, a multiplicity-free CG map still needs basis, normalization and phase conventions. `Hom_G` exists for larger multiplicity without selecting a preferred intertwiner.
- `std::geometry`: ordinary `Scheme`, affine/projective construction, indexed opens, covers, sheaves and checked object gluing; `CInfScheme` and smooth gluing; independent integrable complex and closed nondegenerate symplectic structures; compatible Kähler evidence; appropriate jets. A chart/atlas is not mandated as the only representation. No implicit `Scheme ↔ CInfScheme` coercion.
- `std::analysis`: functional-analytic Banach/dual/distribution objects; **genuinely infinite-dimensional** complex Hilbert spaces with domain-bearing unbounded operators and distinct symmetry/self-adjointness; measure and abstract integration; typed ODE/PDE equations, weak/regular solutions and jet relations. `𝒟`-modules are a **linear** differential-equation specialization, not a representation of arbitrary nonlinear equations. No compulsory numerical probability/sampling subsystem.
- `std::linalg`: finite linear maps, tensor ports, duality, bases and contractions with object/endpoint identity. Neither complex conjugation nor a metric/Hermitian dagger is inserted by tensor contraction. The `Hom_G` equivariance contract is shared with representation theory; sparse/fusion-tree storage is a chosen realization with tracked gauge/basis.
- `std::differential`: geometric/cotangent differentials and the **single mandatory standard numerical AD route**, reverse cotangent pullback. Metrics are required for `grad`; nontrivial selected backward conventions must be named and preserved.
- **Spectral vocabulary:** algebraic finite `eigen(H)` and infinite Hilbert spectral measures use their different declared mathematical profiles.

The names above identify intended responsibility boundaries, **not** a claim that all nested APIs, algorithms or syntax have been implemented or that the exact final module nesting is already frozen.

### 5. Exact coefficients, smooth meaning and numerical realizations

Machine `Float32`, `Float64` and `Complex<Float64>` **MUST NOT** instantiate the exact `Field`/`ExactField` laws needed by exact algebra. In particular, a type checker must not accept a floating-point-coefficient Gröbner basis as an exact-field algorithm without an explicit supported exact reinterpretation/conversion.

Machine floats are not themselves `C∞`-rings. A numerical scalar profile **realizes an ideal real/complex smooth operation** through a declared representation and accuracy/rounding/exception policy. A floating input's finite bit pattern may be interpreted as an exact represented number at an explicit boundary; later machine operations do not thereby become exact field operations.

Certified interval/ball/enclosure arithmetic may be admitted as **separate numerical profiles** with soundness obligations, not as automatic exact-field instances. Native-library choice, ABI, rounding, finite/nonfinite behavior, error estimates and certificate provenance remain visible where required. A numerically successful GEMM/eigensolver is not a proof of a symbolic identity, and different BLAS providers need not return the same bits.

### 6. Differentiation and the extension boundary

For a supported smooth map `f: X → Y`, the standard numerical AD result is a basepoint-indexed **cotangent** pullback

`pullback(f, x, eta): CoTangent<X,x>` with `eta: CoTangent<Y,f(x)>`.

The compiler/std contract may linearize admitted typed IR and structurally transpose the certified linearization using the **algebraic dual pairing**. Reverse execution need not create closures or silently conjugate complex values; `grad` additionally requires an explicit compatible metric. This privileges a verified whole-program route, not a claim that library-based tracing is logically impossible.

Forward mode is a legitimate *third-party interpretation* of admitted smooth programs by base change to a Weil algebra such as `ℝ[ε]/(ε²)`. Although `std::algebra` can construct the quotient ring, this is usable only when `std` smooth primitives (`sin`, `exp`, etc.) expose lawful generic `C∞`/derivative-tower interpretations: a float-only `exp` method is insufficient. Third-party forward interpretation must not require exclusive method edits to `std` owners. The reverse transformation must preserve the coefficient/rule and residual dependencies needed for admitted higher-order composition. The required conformance demonstration is **forward-over-reverse Hessian-vector product**, not merely a stand-alone dual-number demo (tracked in #161). No public standard forward/JVP engine is required.

**Custom pullback contract:** generic owner/capability attachment and checked IR hooks belong to Core; `std::differential` defines linearization/pullback rule semantics and validation obligations; external packages own their concrete implicit/adjoint rules. A rule must retain its function identity, authority/delegation, validity domain, basepoints, scalar/basis/metric restrictions, residuals, evidence status, source/package version and dependency provenance. Imports and successful type checking **MUST NOT** silently turn a third-party rule into a `std`-verified theorem. Unauthorized foreign-function rule injection or a globally winning override is rejected (tracked in #163).

**Optimizer obligation:** the rewrite judgment in differentiable contexts concerns the declared **(primal, selected pullback)** contract, not just primal equality. For example, `relu(x)` and `(x+abs(x))/2` agree as values, but with zero-selected slopes for both nonsmooth primitives at zero their selected backward slopes are 0 and 1/2. Such a rewrite is illegal without an appropriate domain/selected-rule equivalence. On a shared admitted smooth open, ordinary derivative equality can justify a rewrite. Numerical re-association also remains subject to its declared floating-point policy. Coordinate the IR/Lean checker with #159; the concrete optimizer regression is tracked in #164.

### 7. Provenance and acceptance states

Keep at least the following *independent* information dimensions; they are **not** one total trust ranking:

- **Mathematical denotation:** specified object/map, assumptions, equivalence and regularity.
- **Executable support:** unsupported, supported exact/reference profile, or a selected numerical backend with declared preconditions.
- **Proof status:** unverified, assumed, tested, or checked against the actual declarations by admitted Lean-kernel-checkable evidence.
- **Numerical evidence:** unverified estimate, measured residual, certified enclosure or separately proved error bound, with backend/policy identity.
- **Source and authority:** owning function/module/package, rule contributor, delegation, version and dependencies.
- **Physical meaning:** separately stated model/experiment/limit assumptions, not inferred merely from a derivative or solver result.

The checked source-to-IR/Core-to-codegen boundary cannot accept forged evidence, stale assumptions, or a third-party solver's assertion of success as a proof. The general independent semantic-checker architecture and exact Lean acceptance obligations belong to #159 and related implementation issues. This ADR does not assert those checkers have already been implemented.

### 8. Admission and amendment procedure

A frozen charter and a growing mathematics-first standard library are compatible **only if admission is reviewable**. Adding a new `std` family or an operation with materially new semantics **MUST** come through an ADR/amendment proposal containing:

1. **Contract and jurisdiction.** Proposed name/ownership, mathematical target, exact domain and hypotheses, input/output and basepoint identities, structural laws, intended other-`std` interactions, and an explicit Core/`std`/backend split.
2. **Admission argument.** Apply A–D above and explain the denotation's uniqueness up to stated equivalence. Explain why the proposed API is foundational rather than one numerical approximation scheme; identify excluded algorithms and implicit-choice pitfalls.
3. **Execution and evidence profile.** Give an executable reference implementation and independent conformance for **profiles claimed executable**, or explicitly mark an abstract structure as **specification-only** with a worked well-formedness example and unsupported-execution boundary. State checking/proof assumptions, native numerical trust and provenance obligations. Do **not** demand a universal reference evaluator for arbitrary Hilbert spaces, schemes or PDEs.
4. **Negative tests.** Include rejected wrong domains, base/endpoint/coefficient/metric/equivariance/regularity, illicit authority escalation, hidden approximation choices and forged/certification-laundered evidence, as applicable. Identify which tests are proposed versus actually executed.
5. **Compatibility and public-name audit.** Check existing method/function owners, ambiguous dispatch, current public names and prior ADRs. Cross-link the implementation tracker, record version/migration effects and reconcile conflicting draft text without rewriting historical source records.

The new family is admitted by an explicitly reviewed charter change; the prior charter is not silently expanded by an implementation PR, import, popular package, or an internal compiler convenience. The ADR itself can be superseded through a new recorded decision.

### 9. Mathematical alignment and Oracle dependency independence

This amendment records the first, bounded increment of
[#285](https://github.com/MGYamada/Vastitas/issues/285) through the §8 review
procedure. It does not adopt an implementation or completion claim for the
entire future four-package architecture.

**Mathematical alignment and build dependencies are separate contracts.**
Following [#278](https://github.com/MGYamada/Vastitas/issues/278), applicable
`std` mathematical definitions, laws, hypotheses and operation conventions
must agree with the corresponding pinned Lean/mathlib definitions. In
particular, exact field inversion remains totalized at zero; a formula's
applicability hypotheses must still be checked. Machine floats do not acquire
exact field laws. This migration retains mathlib v4.35.0, commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`, as the mathematical reference, not
as an Oracle package requirement. An upstream semantic change requires review;
removing an import is neither a new mathematical definition nor a conformance proof.

The current executable kernel and proof-only Oracle **MUST NOT** depend directly
or transitively on Mathlib. For this increment, `lean/` may require only the
actual local `lean-kernel/`, which itself has no external Lake dependencies.
Both stay on the pinned Lean v4.35.0 distribution. Core proofs replace the
Oracle's rational-cast and sorted-permutation wrappers; the existing pointwise
list correspondence uses a proof-local nil/cons relation instead of a transitive
Batteries import. Existing theorem hypotheses, source-to-Core connections and
proof scope must be preserved. Proof deletion, `sorry`, `admit` and new unproved
axioms are not migration mechanisms.

The official Lean kernel remains authoritative. The allowed axioms remain
exactly `propext`, `Classical.choice`, and `Quot.sound`. An optional independent
export audit cannot replace this acceptance or expand the allowed set.
CI must build and audit the complete Oracle without a Mathlib cache, check
source imports and both Lake configurations/complete manifests, and reject
deliberate direct and transitive dependency regressions. The separate ordinary
compiler CI must continue to work with the Oracle directory absent.

This amendment introduces no public `std` API, executable numerical profile or
new mathematical family. The declaration-local `Forall₂` relation preserves
length and positional correspondence; it does not claim a reusable mathematics
library or occupy Batteries' global name. The associated regression checks and
their execution status are recorded separately from mathematical conformance.
The [verification boundary](../verification.md) documents the changed proof
dependencies and required official build/axiom checks.

Independent `VastitasMath`, separate pinned-Mathlib `VastitasBridge`, conformance
manifests and new correspondence proofs remain subsequent work under #285.
They must not be inferred from this dependency removal. The historical v0.3
source records remain unchanged; current build/contributor documentation is
updated to match this bounded amendment.

## Consequences, validation and migration

- A *thick* foundational `std` can cover algebra, topology/geometry, analysis, infinite-dimensional quantum mechanics and the mathematical formulation of equations, while a potentially infinite space of approximation algorithms remains in the ecosystem.
- The compiler need not know every mathematical object by name. It **does** need stable generic authority, indexed IR and checked evidence interfaces for admitted library contracts.
- The public `std` is not committed to universal solvers, general decidable equality, exact floating-point algebra or automatically differentiable singular/infinite-dimensional operators.
- **This ADR PR is documentary.** Its validation consists of consistency review against [the v0.3 design index](../design.md), #49/#60/#66/#67/#69/#71/#91/#92/#103/#104/#107/#159, and a negative-case/admission audit. It does not implement the exemplar algorithms, claim Lean theorems, or change the compiler/runtime.
- Implementation and executable acceptance, including exact algebra/representation, complex/symplectic geometry, functional/Hilbert/PDE reference examples, third-party AD rules, HVP, equivariant linalg, scalar profiles and optimizer regressions, are tracked in **[#160](https://github.com/MGYamada/Vastitas/issues/160)** and its child/existing issues.
- The historical Draft v0.3 transcription in `docs/design/` remains preserved. To the extent its provisional `§12.5` small-library wording conflicts with this approved charter, this ADR becomes the later normative boundary **upon merge**. Concrete API designs still require their own decisions.

**Principle:** *Standardize the mathematical world and the trusted contracts connecting it; choose algorithms for realizing that world explicitly.*
