# ADR 0001 — Mathematics-first standard-library admission and trust boundary

- **Status:** Adopted for standard-library admission in [PR #166](https://github.com/MGYamada/Vastitas/pull/166).
- **Date:** 2026-10-28
- **Scope:** Standard-library governance and mathematical contracts, **not** a claim of implemented or proved functionality
- **Decision issue:** [#107](https://github.com/MGYamada/Vastitas/issues/107)
- **Implementation tracker:** [#160](https://github.com/MGYamada/Vastitas/issues/160)
- **Dependency boundary:** §9 records the merged local-kernel-only oracle and the separate mathematical bridge. [#285](https://github.com/MGYamada/Vastitas/issues/285) tracks the broader alignment work.
- **Stage 3 admission:** §10 admits `std::differential`, `std::geometry::metric` and `std::geometry::smooth::affine` for the finite smooth affine profile ([#604](https://github.com/MGYamada/Vastitas/issues/604)).

## Context and decision

Vastitas aims to make textbook mathematical objects directly usable in one language for Math 2.0 and Physics 2.0. This requires a substantial, coherent `std`, but does not imply that every useful numerical algorithm belongs there.

**The standard library admits foundational mathematical denotations and the contracts needed to manipulate them; it does not become a catalogue of competing approximation schemes.** The policy below governs new public mathematical operations and families. It freezes **admission rules**, not a closed list of all future standard-library families and not a release deadline.

The word `ε` in the exclusion rule means a numerical approximation tolerance, not a nilpotent element of a Weil algebra.

### 1. Responsibility boundaries

1. **Core:** generic indexed types and identities, ownership/borrowing, function and method authority, dispatch/coherence, generic checked IR, typed evidence validation and structural compiler transformations. No growing set of special-case privileges keyed by the spelling of a mathematical type.
2. **Mathematical `std`:** ordinary versioned `.vast` definitions and contracts for mathematical structures, maps, invariants, equations and supported exact/reference operations. Where necessary it exposes checked interfaces for admitted primitive/derivative rules and realization boundaries. Abstract definitions may exist without a universal evaluator.
3. **Ecosystem and selectable backends:** algorithms that approximate or realize mathematical targets using mesh, time step, polynomial degree as a refinement parameter, sampling, cutoff, stopping criteria, tolerance, resource schedule or backend-specific numerical behavior. Examples include quadrature, ODE/PDE solvers, optimizers, sparse iterative eigensolvers, Monte Carlo, DMRG/VUMPS and high-performance kernels.

In the current implementation plan, `monad` owns explicit computational
policies and effects, and `nature` owns physical interpretations, conventions
and uncertainty. Mathematical denotations remain in `std`. The governing
issues distinguish these roles from Core and ecosystem algorithms. The
[architecture tracker](https://github.com/MGYamada/Vastitas/issues/386) records
the status of the broader ADR amendment.
[Current jurisdiction, #304](https://github.com/MGYamada/Vastitas/issues/304)

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

#### Daleckii–Krein mathematical foundation (bounded addition, 2026-11-02)

Introduce `lean-bridge/` as an independent, proof-only Lake package for the
important [Daleckii–Krein theorem](../daleckii-krein.md). It uses the exact
Mathlib reference and Lean version in §9. Its initial dependency is only pinned
Mathlib and its locked transitive packages; it is not a library target inside
`lean/`, nor a dependency of the kernel, Oracle, runtime or ordinary build.
Separate CI builds it, audits all bridge declarations against the unchanged
three-axiom allowlist, and replays its proof modules with the official kernel.

The result identifies the real Fréchet derivative of Mathlib's actual continuous
functional calculus at a finite-spectrum self-adjoint element. Its complex
Hermitian matrix specialization includes repeated eigenvalues. This is a
mathematical foundation for future spectral AD, not a public `std` operation,
an executable spectral algorithm or a proof about a fabricated Core model.
The documentation fixes the exact hypotheses and records the missing
representation, cotangent-rule and source/native correspondence obligations.

This increment introduces no public mathematical family or method authority,
and does not complete #285's four-package architecture. `VastitasMath` and the
implementation correspondence layer remain future work. The kernel/Oracle
dependency policy in §9 stays closed; future bridge imports of implementation
or independent mathematics packages require an explicit policy amendment.

Independent `VastitasMath`, conformance manifests and new correspondence proofs
remain subsequent work under #285. The first separate pinned-Mathlib
`VastitasBridge` package is the bounded mathematical increment described above.
The oracle dependency boundary and the mathematical correspondence obligations are verified separately.

### 10. Smooth affine differentials and metrics (amendment, 2026-11-04)

This amendment admits two families through the §8 procedure:
`std::differential` and `std::geometry::metric`. It also admits the module
`std::geometry::smooth::affine` under the `std::geometry` family of §4. All
three serve the finite profile of historical Stage 3. The amendment also
records the decision that a smooth manifold has no type of its own. It admits
these contracts; it does not claim that they are implemented or proved. The
History section at the end of this chapter links the tracker and the issues
that this section refers to.

#### Terms

- A *smooth affine object* is a declared smooth real affine space
  `Affine(n)[c₁, …, cₙ]` with named coordinates. It denotes `ℝⁿ`.
- A *sealed classification* is a classification whose members are fixed by its
  declaration. The smooth affine objects form the sealed classification
  `CInfAffine`.
- A *seed* is the covector that a pullback starts from.
- *Executable kernel* means the Vastitas checker and runtime in
  `lean-kernel/`, written in Lean. It is distinct from the official Lean
  kernel of §9.
- The *wire* is the JSON request from the Rust frontend to the executable
  kernel.

#### Contract and jurisdiction

- **Smooth affine objects.**
  - Each declaration introduces one object. Two declarations of the same
    dimension introduce different objects.
  - Smooth affine objects belong to `CInfAffine`. They must not index the
    Stage 1 `Scheme` or `CInfScheme` families, or the Stage 2 presented
    families. Objects of those families must not index the smooth families.
  - Reconciling `CInfAffine` with the Stage 1 `CInfScheme` remains open.
- **Smooth maps.**
  - A smooth map `ℝⁿ → ℝᵐ` is given by `m` polynomials with exact rational
    coefficients in the source coordinates. It denotes the real polynomial
    map.
  - Two smooth maps are equal when their coordinate polynomials are equal.
    Over ℝ this is equality of the real maps.
- **No manifold type.**
  - A smooth manifold is a `CInfScheme` object together with checked
    `IsSmoothManifold(X, n)` evidence. That evidence requires Hausdorffness,
    second countability and locally standard C∞ charts.
  - There is no `Manifold`, `CInfManifold` or `Variety` type, and no
    `std::geometry::smooth::manifold` module.
  - Gluing and `IsSmoothManifold` evidence are outside this amendment.
- **`std::differential`** owns metric-free differentiation, the
  `pullback(f, x, eta)` of §6. This supersedes the earlier assignment of metric-free
  differentiation to `std::geometry::smooth`.
  - For a smooth map `f`, a point `x` and a seed `η` over `f(x)`, the pullback
    is the covector `η ∘ Df(x)` over `x`.
  - In this profile, points are run-time values, so the basepoint index of §6
    is checked at run time. A seed over another point gives the failure value
    ⊥. ⊥ is absorbing, and it equals no covector.
  - The differential `dφ` at `x` of a smooth function `φ: X → Affine(1)` is the
    pullback of the coordinate covector `dt` at `φ(x)`.
  - `std::differential` also owns `gradient(φ, x, using = g, evidence = e)`,
    the `grad` of §4 and §6. It is the ordinary library composition
    `sharp(dφ_x, using = g, evidence = e)`, not a differentiation primitive.
    This also supersedes the earlier assignment of `gradient`
    to `std::geometry::metric`.
- **`std::geometry::metric`.**
  - A metric `MetricForm<X>` is a symmetric bilinear form on a smooth affine
    object. It is given by a symmetric rational Gram matrix `G` in the declared
    coordinates of `X`.
  - Evidence is declared separately. It has two kinds, `nondegenerate(g)` and
    `riemannian(g)`, and it names the metric it certifies.
  - `flat(v, using = g)` maps a vector `v` at `x` to the covector `Gv` at `x`.
  - `sharp(α, using = g, evidence = e)` maps a covector `α` at `x` to the
    vector `G⁻¹α` at `x`. `e` must be `nondegenerate(g)` evidence;
    `riemannian(g)` evidence is the wrong kind for `sharp`.
  - The general metric design requires `IsSmoothManifold` evidence for its
    base. This profile uses
    declared smooth affine objects only.
- **Split between Core, `std` and backends.**
  - Core supplies generic indexed families, checked declarations, evidence
    records and code generation. Core gains no rule keyed by a type name.
  - `std` declarations bind the executable kernel's runtime routines as
    primitives, as the Stage 2 presented-algebra profile does.
  - The reverse pass is a runtime routine of the executable kernel. The
    compiler emits no reverse Core in this profile. The
    [amendment of 2026-11-06](#compiled-reverse-core-amendment) admits
    compiled reverse Core and keeps this routine for the steps that compiled
    Core does not open.
  - The executable kernel checks every declaration before code generation.
  - There is no selectable backend. Floating-point backends are outside this
    profile.

#### Laws

- The pullback is linear in the seed.
- Pullback along the identity is the identity.
- Pullback along `g ∘ f` at `x` equals pullback along `g` at `f(x)` followed by
  pullback along `f` at `x`.
- `sharp(flat(v)) = v` and `flat(sharp(α)) = α` for a metric with
  nondegeneracy evidence (the `using` and `evidence` arguments are elided).

#### Admission argument

- **A, intrinsic denotation.**
  - The pullback of a seed `η` is `Df(x)ᵀη = η ∘ Df(x)`, where `Df(x)` is the
    Fréchet derivative of the real polynomial map at `x`. It does not depend on
    the algorithm that computes it.
  - Two covectors over one point are equal when their components in the dual
    basis of the declared coordinates are equal.
  - `flat` and `sharp` are the linear maps given by `G` and `G⁻¹`.
- **B, foundational target.**
  - The pullback is the action of the cotangent functor on a smooth map at a
    point.
  - `flat` and `sharp` are the musical isomorphisms of a selected metric.
  - Finite differences and floating-point AD are realizations, not this
    denotation.
- **C, no hidden numerical choice.**
  - Arithmetic is exact over the rationals.
  - The profile infers no metric, including the Euclidean metric.
  - Nondegeneracy and positivity are never inferred from a sample, a tolerance
    or a type name.
- **D, contract.**
  - Basepoints, objects and variance (vector or covector) are explicit.
  - A wrong object, a wrong variance or a wrong metric selection is a static
    error. A wrong basepoint gives ⊥.
  - Polynomial maps are smooth on all of ℝⁿ, so the profile has no domain or
    regularity hypothesis.
  - The planned Stage 3 acceptance map must keep four kinds of claim
    apart:
    - structural facts about the runtime, whose proofs belong in the oracle;
    - the Fréchet comparison, whose proof belongs in the mathlib bridge;
    - the polynomial Kähler comparison, whose proof belongs in the mathlib
      bridge;
    - tests, which are evidence but not proofs.

#### Execution and evidence profile

- **Executable profile.** The profile consists of:
  - exact rational polynomial maps between smooth affine objects of dimension
    at most 16, the value of the `algebraGenerators`
    [limit](../appendix/limits.md). The implementation records this use in
    that table;
  - rational points;
  - constant rational metrics.
- **Saved and recomputed forward values.**
  - The *saved-tape* reverse pass stores every intermediate point during a
    forward pass.
  - The *recomputing* reverse pass evaluates each intermediate point again.
  - Both passes must give the same covector.
- **Scalars.** Exact rationals stay inside the runtime. They surface as `Int`
  inputs and `Pair<Int>` observations.
- **Wire.** The profile uses protocol 9 only. Protocols 7 and 8 are an error
  (`E_PROTOCOL`).
- **Independent reference.**
  - The executable kernel must match a fixture generated from
    `scripts/metric_free_reference.py` and `scripts/metric_reference.py`.
  - These references cover the real plane only: maps ℝ² → ℝ², functions
    ℝ² → ℝ and 2 × 2 Gram matrices. Dimensions 3 to 16 have no independent
    reference.
- **Certificates.**
  - Nondegenerate evidence is an exact inverse. Riemannian evidence is an exact
    `L D Lᵀ` factorization with positive `D`.
  - The executable kernel must compute each certificate and check it again
    before acceptance. Certificates never come from the wire.
  - Evidence is sound because the kernel re-checks it. That the kernel's
    certificate computation succeeds for every invertible or
    positive-definite form is tested, not proved.
- **Trust.** Native tests are evidence, not proofs. Native refinement of the
  runtime is not claimed.

#### Outside this admission

- Compiler-emitted reverse Core. The
  [amendment of 2026-11-06](#compiled-reverse-core-amendment) admits it within
  its boundary.
- The forward-over-reverse Hessian-vector product that §6 requires, with its
  Weil-lift semantics. This profile does
  not discharge that requirement. Forward mode stays a third-party
  interpretation (§6).
- C∞-ring differentials as modules. This amendment does not admit
  them.
- Custom derivative rules and non-polynomial primitives. Without custom
  rules, authority escalation does not apply.
- Complex AD, closures and checkpointing
  beyond save-all and recompute-all.
- Gluing and `IsSmoothManifold` evidence.
- Position-dependent metrics, `signature`, `causal_kind` and orthogonal
  complements.
- Floating-point realizations and performance.

#### Negative tests

The Stage 3 profile must reject each of the following with its own diagnostic.
The [Stage 3 acceptance map](../stage3-acceptance.md#acceptance-conditions)
records the test that runs each case. A case without a test there remains
proposed.

- **Objects:** an implementation mismatch, a dimension that differs from the
  coordinate count, `spec` under a smooth implementation, and a smooth global
  (`E_SMOOTH`).
- **Families:** smooth objects in Stage 1 or Stage 2 families, and the reverse.
- **Maps:** a map whose image polynomials use the target's coordinates instead
  of the source's.
- **Pullbacks:**
  - a seed over another object;
  - a vector where a covector is required;
  - a tape from another point.
- **Metrics:**
  - an asymmetric, wrong-size, non-constant or foreign-object metric;
  - an omitted metric, including an implicit Euclidean default;
  - an ambiguous metric selection.
- **Evidence:**
  - a singular metric claimed nondegenerate;
  - an indefinite metric claimed Riemannian;
  - `sharp` without evidence, with wrong-kind evidence, or with evidence for
    another metric.
- **Inputs and transport:** floating-point inputs, protocols 7 and 8, a wire
  payload that carries a certificate, and tampered Core.

The profile must also show failure semantics: a seed over another point
gives ⊥, and ⊥ propagates through a wrong intermediate basepoint.

#### Compatibility and public-name audit

- **Operation names.**
  - `std::differential` admits `pullback`, `differential`, `linearize`,
    `backward` and `gradient`. `pullback` is the operation of §6, and its wire
    operation is `cotangent_pullback`. `gradient` is the `grad` of §4 and §6.
    The standard library exports the first four; see the deviation below.
  - The smooth map type is `Smooth<X, Y>`, and the tape type is `Tape<X, Y>`.
  - These names must not shadow existing names. Smooth-map `compose` and the identity must not be ambiguous
    with `std::geometry::compose` and `std::geometry::smooth::id`.
- **`MetricForm`.**
  - `MetricForm` is nominally distinct from the protocol-8 diagonal Hermitian
    `Metric`. Neither converts to the other.
  - `MetricForm` is also distinct from `MetricSpace`.
- **`Affine` forms.**
  - The declaration forms `Affine(n)[c₁, …, cₙ]` and `Affine(K, n)[…]` appear
    in declarations only. `Affine(K, n)[…]` is sugar for the Stage 2
    `spec[…] over K`.
  - In function bodies, `Affine(n)` keeps its Stage 1 meaning as the
    descriptor primitive of `std::geometry::scheme` or `std::geometry::smooth`.
  - `geometry_compat` resolves `Affine(QQ, n)` and `Affine(CInfReal, n)`.
  - A smooth affine declaration names its implementation, for example
    `SmoothR`. So the goal of declaring smooth space without naming a `CInfReal`
    implementation is met only partly.
- **Packages.**
  - The `std::differential` package depends on the geometry package, including
    `std::geometry::metric`.
  - The geometry package does not depend on `std::differential`.
  - The pullback and `differential` must not depend on any metric declaration.
- **Versions and migration.**
  - The profile adds no wire protocol version.
  - Existing programs keep their meaning.
  - The protocol-8 `Metric` keeps its name. A rename is a separate decision.

#### Deviation: no `gradient` export

The standard library implements this amendment without a `gradient` export.
A library function cannot be generic over the application's smooth affine
object, because the smooth families take declared objects only. It also cannot
take a metric, its evidence or `sharp` as a parameter. An application
therefore writes `gradient` as an ordinary function that applies its own
`sharp` to `differential`. This meets the contract above, because `sharp`
requires a named metric and nondegenerate evidence. The admission of
`gradient` stands. The History section names the follow-up.

<a id="compiled-reverse-core-amendment"></a>

#### Amendment: compiled reverse Core (2026-11-06)

This amendment admits compiled reverse Core for the finite profile of this
section, through the §8 procedure. It changes no public name, operation, wire
form or protocol version. It changes how the executable kernel realizes
`pullback`, `differential` and `backward`. It admits the contract; the
[compiled reverse Core acceptance map](../reverse-core-acceptance.md) records
what is implemented, tested and proved.

- **Contract.**
  - After acceptance, the executable kernel may replace a reverse pass by Core
    that it generates from the checked Core. Forward Core computes the primal
    value and the residual points as ordinary Core values. A generated
    backward function computes the pullback from the residuals and the seed.
  - The generated Core must denote the operation that it replaces: the
    covector `η ∘ Df(x)` over `x` for a seed over `f(x)`, and ⊥ for any other
    seed.
  - The derivative rule of each primitive is part of its registry entry. A
    declared polynomial map is pulled back by its Jacobian table, which the
    executable kernel computes from the map with exact rational coefficients.
  - A map whose structure the compilation does not open is one step. The
    runtime routine of this section pulls the seed back along it, so that
    routine stays part of the profile.
  - The saved policy passes every residual to the backward function. The
    recomputed policy passes the input point, and the backward function
    evaluates the other residuals again. Both must give the same covector.
  - Residuals are immutable pure Core values. They meet the retention
    contract of
    [storage ownership §7.10](../storage-ownership.md#710-reverse-residual-retention-and-mutation)
    as Retain or Recompute, without storage.
- **Admission argument.** The denotation of the pullback (A) does not depend
  on the algorithm that computes it. Compiled Core and the runtime routine are
  two realizations of it, not two denotations (B). Arithmetic stays exact, and
  no derivative is sampled or approximated (C). Basepoints, objects and
  variance stay explicit (D).
- **Checking.**
  - The generated module passes the Core audit that source-derived Core
    passes.
  - Translation validation compiles the source module again and compares
    the result.
  - No source and no wire request can name or supply the generated
    declarations, functions or residuals.
  - A failed check is an internal error. The compilation rejects no accepted
    program: a reverse pass that it cannot compile stays a call of the runtime
    routine.
- **Evidence obligations.**
  - The oracle proves, without mathlib, what the generated forward and
    backward Core compute, that the two policies agree, and their meaning
    relative to the oracle chain rule.
  - The mathlib bridge proves that the generated backward Core is the
    adjoint of the Fréchet derivative, independently of the kernel chain rule.
  - The rewrite of one call is a local theorem with explicit premises.
    Agreement of whole compiled modules with their source is tested, not
    proved.
- **Boundary.** Outside this amendment:
  - differentiation of branches, loops or recursion; a branch may still
    choose a map, which is then one opaque step;
  - compiled Core for opaque steps, for tapes that cross a function boundary,
    and for `composite`;
  - floating-point realizations and performance;
  - optimizer preservation of the (primal, selected pullback) contract of §6;
  - custom rules, forward mode, the Hessian-vector product, complex AD and
    checkpointing beyond save-all and recompute-all, as listed above.

## Consequences, validation and migration

- A *thick* foundational `std` can cover algebra, topology/geometry, analysis, infinite-dimensional quantum mechanics and the mathematical formulation of equations, while a potentially infinite space of approximation algorithms remains in the ecosystem.
- The compiler need not know every mathematical object by name. It **does** need stable generic authority, indexed IR and checked evidence interfaces for admitted library contracts.
- The public `std` is not committed to universal solvers, general decidable equality, exact floating-point algebra or automatically differentiable singular/infinite-dimensional operators.
- This ADR governs admission. Executable and proof acceptance for specific families remain tracked in [#160](https://github.com/MGYamada/Vastitas/issues/160).
- Implementation and executable acceptance, including exact algebra/representation, complex/symplectic geometry, functional/Hilbert/PDE reference examples, third-party AD rules, HVP, equivariant linalg, scalar profiles and optimizer regressions, are tracked in **[#160](https://github.com/MGYamada/Vastitas/issues/160)** and its child/existing issues.

**Principle:** *Standardize the mathematical world and the trusted contracts connecting it; choose algorithms for realizing that world explicitly.*

## History

§10 was adopted for the Stage 3 tracker
[#604](https://github.com/MGYamada/Vastitas/issues/604), through PR
[#609](https://github.com/MGYamada/Vastitas/pull/609). It records the decision of
[#360](https://github.com/MGYamada/Vastitas/issues/360). Its references are:

- **Ownership.** It supersedes the ownership lines for metric-free
  differentiation (§1) and `gradient` (§2) in
  [#264](https://github.com/MGYamada/Vastitas/issues/264). That issue also keeps
  position-dependent metrics, signature algebra (§3) and the protocol-8
  `Metric` rename.
- **Constructors and gluing.** Reconciling `CInfAffine` with `CInfScheme`, and
  the `CInfReal`-free constructor, remain in
  [#103](https://github.com/MGYamada/Vastitas/issues/103). Gluing and
  `IsSmoothManifold` evidence are tracked in
  [#606](https://github.com/MGYamada/Vastitas/issues/606).
- **Outside the admission:**
  - compiler-emitted reverse Core: [#361](https://github.com/MGYamada/Vastitas/issues/361),
    [#290](https://github.com/MGYamada/Vastitas/issues/290),
    [#164](https://github.com/MGYamada/Vastitas/issues/164);
  - the Hessian-vector product and C∞-ring modules:
    [#161](https://github.com/MGYamada/Vastitas/issues/161),
    [#381](https://github.com/MGYamada/Vastitas/issues/381);
  - custom rules: [#163](https://github.com/MGYamada/Vastitas/issues/163);
  - complex AD, closures and checkpointing:
    [#71](https://github.com/MGYamada/Vastitas/issues/71),
    [#570](https://github.com/MGYamada/Vastitas/issues/570),
    [#544](https://github.com/MGYamada/Vastitas/issues/544);
  - performance: [#222](https://github.com/MGYamada/Vastitas/issues/222).
- **Compiled reverse Core.** The amendment of 2026-11-06 was adopted for
  [#623](https://github.com/MGYamada/Vastitas/issues/623), after the primitive
  descriptors of [#622](https://github.com/MGYamada/Vastitas/issues/622). It
  admits, for this profile, the compiler-emitted reverse Core that §10
  excluded when it was adopted. [#361](https://github.com/MGYamada/Vastitas/issues/361)
  and [#290](https://github.com/MGYamada/Vastitas/issues/290) keep the general
  cases, [#164](https://github.com/MGYamada/Vastitas/issues/164) the optimizer
  obligation, and [#629](https://github.com/MGYamada/Vastitas/issues/629) the
  sharing of Jacobian tables.
- **Gradient export.** Exporting a generic `gradient` from
  `std::differential` needs object-polymorphic signatures and metric
  parameters: [#626](https://github.com/MGYamada/Vastitas/issues/626).
- **Names and protocol.** `MetricSpace` belongs to
  [#382](https://github.com/MGYamada/Vastitas/issues/382), and the single-protocol policy
  to [#533](https://github.com/MGYamada/Vastitas/issues/533).
