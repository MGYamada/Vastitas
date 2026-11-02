# ADR 0001 — Mathematics-first standard-library admission and trust boundary

- **Status:** Accepted (ratified by PR #166 on 2026-10-28); subsequent changes require the §8 amendment procedure
- **Date:** 2026-10-28
- **Scope:** Standard-library governance and mathematical contracts, **not** a claim of implemented or proved functionality
- **Decision issue:** [#107](https://github.com/MGYamada/Vastitas/issues/107)
- **Implementation tracker:** [#160](https://github.com/MGYamada/Vastitas/issues/160)
- **Dependency amendment (2026-10-30):** §9 was ratified by merged [PR #288](https://github.com/MGYamada/Vastitas/pull/288) as the first bounded migration increment of [#285](https://github.com/MGYamada/Vastitas/issues/285); the remaining four-package architecture and conformance proofs remain open.

## Context and decision

Vastitas aims to make textbook mathematical objects directly usable in one language for Math 2.0 and Physics 2.0. This requires a substantial, coherent `std`, but does not imply that every useful numerical algorithm belongs there.

**The standard library admits foundational mathematical denotations and the contracts needed to manipulate them; it does not become a catalogue of competing approximation schemes.** The policy below governs new public mathematical operations and families. It freezes **admission rules**, not a closed list of all future standard-library families and not a release deadline.

The word `ε` in the exclusion rule means a numerical approximation tolerance, not a nilpotent element of a Weil algebra.

### 1. Five semantic responsibilities, three user-facing library families

These are **responsibility roles**, not five consecutive import layers. The three user-facing library families `std`, `monad`, and `nature` are governed by mathematical versus operational versus physical meaning (#304). Their dependency graph is intentionally acyclic.

1. **Core:** generic indexed identities and types, whole-function ownership/borrowing, explicit authority/delegation, dispatch/coherence, checked IR, evidence validation and structural compiler transformations. It owns no expanding mathematical-type-specific privileged exception.
2. **Mathematical `std`:** the closed mathematical and pure reference universe: selected mathematical objects, models, maps, laws and exact/reference denotations, with all mathematical parameters and hypotheses explicit. This includes finite reference formats when independently admitted; it excludes hidden runtime, physical identification and selected approximation algorithms. Abstract meanings need not have universal executable representatives.
3. **`monad`:** opt-in **operational/computational interpretations and policies**: failure and sequencing, resource/capability effects, selected numerical execution and flag observations, asynchronous/parallel/device execution adapters. The package name does *not* assert that each submodule is an instance of the categorical Monad: each module must declare whether it supplies a certified Monad, graded effect, or a non-monadic execution/policy adapter. Mere import grants neither authority nor mandatory monadic syntax.
4. **`nature`:** pure **empirical/physical interpretations** that attach selected physical meaning to mathematical objects without changing the mathematical denotation. Fundamental families are `dimension` (quantities/units), `error` (measurement/model uncertainty) and `symmetry` (selected physical actions), plus facade-only `vector3d` and `relativity` (#299–#301/#372/#373). It does not own a second mathematical theory, a device effect or a general physics-algorithm catalogue.
5. **Ecosystem / Harness:** optional numerical algorithms, simulations, security/physical protocols, scientific applications, measurements, experiment-specific models and explicit bridges combining the above. Selected approximation schedules, iterative solvers, DMRG, Monte Carlo, device orchestration and empirical comparisons belong here or in a specified execution adapter. **First-party bundled realization backends** (e.g. OpenBLAS/C ABI and native sparse kernels, #92/#243) are supported infrastructure rather than mathematical `std` definitions or independent user-facing families. They implement checked Core/`std` contracts behind explicit `monad`/backend execution policy, numerical/ABI provenance and refinement obligations; bundled code does not inherit proof authority.

**Dependency rule:** Core is the trusted base; `std → Core`, `monad → std`, `nature → std`, and the ecosystem may consume all three. `std` MUST NOT import `monad` or `nature`, and no foundational `monad` or `nature` package imports the other; device/measurement bridges live in the ecosystem. Specialized proof-only dependencies (`VastitasMath`, Oracle, Bridge) are governed separately by §9/#285. Package splitting and revision policies must respect these dependencies; they do not silently create new completed public packages.

An operation may have a mathematically pure implementation yet belong to `monad` because its **semantic responsibility** is an opt-in execution/failure policy. Conversely, explicit mathematical choices (e.g. metric, measure, topology, term order) remain in `std` when they determine a mathematical object and are stated as data. A finite IEEE bit-pattern/reference-operation contract can be `std::ieee754` after admission; FMA/ABI/native sequencing and flag observation are `monad::float` / backend matters (#244/#318/#322). Numerical approximation/truncation error, statistical sampling uncertainty and physical measurement/model uncertainty are distinct responsibilities.

**Admission rule for `monad`:** require a declared target computational interpretation, its effects/capabilities (or explicit absence), laws/evaluation order/failure behavior, ownership/cancellation/cleanup, source-to-accepted-Core refinement and negative tests. Abstract Monad and its Kleisli category belong to `std::category`; strong/commutative Monad structures and PROPs that need a selected monoidal product, and graded monoidal laws, belong downstream to `std::monoidal` (#199/#201/#204). The strength is *data* in closure-free Core, not inferred from unavailable capture/currying; an execution module that is not itself a Monad must say so (#199/#206/#207/#303). Physical admission follows #304's two-tier foundational/facade test; a convention alone is insufficient unless it changes or records which physical quantity/action/world interpretation is selected.

**Constructive fast `std::structure`:** algorithm-first named operations have selected, revision-bound ordinary `.vast` bodies and mandatory declared correctness claims. Apply #184 to all code: Ownership/Borrow and Core Safety are mandatory, while every mathematically applicable Domain obligation is also mandatory; there is **no namespace-wide Ownership/Borrow-only exemption**. Extensional set/group/ring claims require independent Lean evidence bound to the accepted Core. Finite group/ring tables are *presentations and checked constructors of #311/#312 models*, not independent competing `FinGroup`/`FinRing` mathematical types (#263/#401/#402). No CS/MS/CF or Universe Charter exception is created.

A Core mechanism may support a mathematical `std` contract without making its concrete mathematical operations compiler intrinsics. Importing a package must not silently expand edit authority, executable capabilities, physical claims or the trusted proof boundary.

### 2. Normative admission test

A proposed `std` mathematical operation **MUST** document all of the following.

**A. Mathematical denotation, or named computational algorithm (see §2A′).** Mathematical `std` operations have an implementation-independent denotation with explicit data and hypotheses (coefficient domain, order, topology, measure, domain, representation, metric, branch or phase). Two exact implementations target that denotation up to the **declared equivalence/canonical form**. A `std::structure` named algorithm instead has an explicit versioned accepted `.vast` operational body and a **mandatory stated result claim**, with checked evidence status. Neither names nor matching shapes establish identity.

**A′. Computational operations and representation-dependence (`std::structure` only).** For each public named operation declare its inputs, chosen representation, observable behavior, error/termination boundary, **required correctness claim** (e.g. sorted permutation or stable sorted permutation), extensional equivalence and evidence status (`specified`, `tested`, `kernel-proved`, `conditional`, `unsupported`). Distinguish:
- **Invariant** operations, which descend along the declared quotient/equivalence and meet §2A's result-denotation test (e.g. `FinSet.contains/cardinality`, DSU `same/size/count`, and stable sorting under a lawful total preorder; use Lean core's `List.mergeSort` lemmas when suitable).
- **Representation-dependent** operations, which are only meaningful relative to an explicit representation/view and must not masquerade as extensional maps (e.g. quicksort equal-key order, DSU `find` root, HashMap iteration and order-sensitive FinSet traversal). Changing an observable pivot/tie/iteration policy is an API/revision change; a correct quotient lift needs a checked well-definedness relation (#350).
A named algorithm's body fixes **execution**, not an automatic proof of its promised sorting/search/data-structure postcondition. A claim is mandatory even when a proof is pending. #389/#391/#394/#395/#399 are design owners; #388 freezes the release subset.

**B. Foundational target, not a selected approximation protocol.** The public operation specifies an object, map, invariant, equation or structurally canonical computation in the mathematical theory itself. Its meaning is **not** the output of one chosen iterative/discretization/sampling strategy for approximating a different target. A refinement count or stopping rule supplied to obtain an approximate answer remains a realization policy, even if that algorithm is deterministic and well defined.

**C. No hidden numerical choice in the mathematical result.** The denotation MUST NOT depend on a default approximation tolerance, mesh, sampling rule, truncation threshold, convergence check, numeric branch heuristic or secretly chosen solver. Resource exhaustion may produce a reported failure or unsupported result; it must not silently redefine success. Mathematical choices that truly change the object (e.g. a term order, measure or boundary condition) are explicit **semantic data**, not hidden numerical options.

**D. Law, domain, equivalence and evidence contract.** State algebraic/analytic hypotheses, relevant domains, regularity, object/basepoint identity, equality notion, admissible scalar/profile, error and failure behavior, and which obligations are checked, assumed or not supported. No general termination, existence, equality decision, numerical guarantee or formal theorem may be inferred from an abstract type name.

The test is **necessary but not an automatic theorem of admission**. A mathematical formula can define an unbounded number of distinct algorithms. A proposal must justify that its public operation is foundational rather than simply one selectable method in an approximation family. Admission decisions, including exclusions, are made explicitly and versioned through the procedure below.

### 3. Deliberate positive and negative boundary examples

| Mathematical target in `std` | Permitted implementation / external realization | Deliberate exclusion from the `std` semantic API |
| --- | --- | --- |
| Reduced Gröbner basis over an admitted **exact field**, with fixed monomial order | Buchberger or F4 and independently checked certificates | Claims that machine Float satisfies exact `Field` laws or an effective exact-arithmetic capability, or an unspecified term order |
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
- `std::geometry`: ordinary `Scheme`, affine/projective constructions, indexed opens, covers, sheaves and checked object gluing; separate `CInfScheme` and smooth gluing; and appropriate jets. Algebraic-variety and smooth-manifold classifications are independently checked `IsVariety` / `IsSmoothManifold` properties on the relevant schemes, **not** standalone `Variety` / `Manifold` abstract types or privileged modules (#360). `std::geometry::complex` owns almost-complex structure (`J² = -id`) only; integrability is a separately proved property, not an implicit std guarantee. `std::geometry::symplectic` owns closed, nondegenerate forms and their exact evidence under existing checkers (#211). Kähler geometry is a downstream ecosystem composition of these mathematical ingredients and additional compatible integrability/metric proofs, **not** a privileged std namespace or new checker. Charts/atlases are optional local certificates rather than mandatory stored representations. No implicit `Scheme ↔ CInfScheme` coercion.
- `std::analysis`: functional-analytic Banach/dual/distribution objects; **genuinely infinite-dimensional** complex Hilbert spaces with domain-bearing unbounded operators and distinct symmetry/self-adjointness; measure and abstract integration; typed ODE/PDE equations, weak/regular solutions and jet relations. `𝒟`-modules are a **linear** differential-equation specialization, not a representation of arbitrary nonlinear equations. No compulsory numerical probability/sampling subsystem.
- `std::linalg`: finite linear maps, tensor ports, duality, bases and contractions with object/endpoint identity. Neither complex conjugation nor a metric/Hermitian dagger is inserted by tensor contraction. The `Hom_G` equivariance contract is shared with representation theory; sparse/fusion-tree storage is a chosen realization with tracked gauge/basis.
- `std::differential`: universal C∞ differentials, comparison with analytic Fréchet and polynomial Kähler profiles, certified reverse cotangent pullback and mathematical Weil/HVP semantics (#381/#161). Reverse mode is the **single mandatory standard numerical AD route**; a metric is required for vector `grad`, not cotangent HVP. Selected backward conventions remain explicit.
- `std::structure`: constructive finite algorithms and containers; exact claims are divided between extensional/invariant and explicitly representation-dependent operations under §2A′. `FinSet` is an executable set presentation; `fingroup`/`finring` are table/certificate fronts to the existing #311/#312 Lawvere models, not new mathematical types. Named sorting claims are mandatory even when only tested; C/C++ parity is a measurement target (#263/#389/#391/#401/#402).
- `std::validated`: finite proof-carrying numerical enclosures and certificate interpretation (#244/#293), separate from exact polynomial/field algorithms and native rounding/FMA policy.
- `std::ieee754`: explicitly named pure finite IEEE reference contracts (#322), distinct from the `monad::float` execution/flag policy and first-party bundled realization backends.
- **Spectral vocabulary:** algebraic finite `eigen(H)` and infinite Hilbert spectral measures use their different declared mathematical profiles.

The names above identify intended responsibility boundaries, **not** a claim that all nested APIs, algorithms or syntax have been implemented or that the exact final module nesting is already frozen.

### 5. Exact coefficients, smooth meaning and numerical realizations

Machine floating-point representations **MUST NOT** instantiate the exact mathematical `Field` laws or satisfy an effective exact-arithmetic algorithm's requirements by name. `ExactField` is **not** a separate mathematical theory: a supported exact algorithm requires a selected `Field` model plus verified computational capabilities (effective exact operations, equality/zero decisions and applicable evidence; #313). Historical prose mentioning `Float32`, `Float64` and `Complex<Float64>` is **not** the implemented syntax: the present resource parser accepts bare `F64` and `Complex<F64>`. #318/#322 propose typed `F32<RR>`, `F64<RR>` and `F64<CC>` representations; migration must resolve bare-`F64` ambiguity by edition/versioned desugaring or explicit rejection and preserve source provenance, with finite IEEE reference semantics separate from `monad::float` execution policy. In particular, a type checker must not accept a floating-point-coefficient Gröbner basis as an exact-field algorithm without an explicit supported exact reinterpretation/conversion.

Machine floats are not themselves `C∞`-rings. A numerical scalar profile **realizes an ideal real/complex smooth operation** through a declared representation and accuracy/rounding/exception policy. A floating input's finite bit pattern may be interpreted as an exact represented number at an explicit boundary; later machine operations do not thereby become exact field operations.

Certified interval/ball/enclosure arithmetic may be admitted as **separate numerical profiles** with soundness obligations, not as automatic exact-field instances. Native-library choice, ABI, rounding, finite/nonfinite behavior, error estimates and certificate provenance remain visible where required. A numerically successful GEMM/eigensolver is not a proof of a symbolic identity, and different BLAS providers need not return the same bits.

### 6. Differentiation and the extension boundary

For a supported smooth map `f: X → Y`, the standard numerical AD result is a basepoint-indexed **cotangent** pullback

`pullback(f, x, eta): CoTangent<X,x>` with `eta: CoTangent<Y,f(x)>`.

The compiler/std contract may linearize admitted typed IR and structurally transpose the certified linearization using the **algebraic dual pairing**. Reverse execution need not create closures or silently conjugate complex values; `grad` additionally requires an explicit compatible metric. This privileges a verified whole-program route, not a claim that library-based tracing is logically impossible.

Forward mode is a legitimate *optional execution interpretation* of admitted smooth programs; `std::differential` owns the mathematical Weil-lift and forward-over-reverse/HVP comparison semantics (#381/#161), while third-party packages may supply execution engines. It uses base change to a Weil algebra such as `ℝ[ε]/(ε²)`. Although `std::algebra` can construct the quotient ring, this is usable only when `std` smooth primitives (`sin`, `exp`, etc.) expose lawful generic `C∞`/derivative-tower interpretations: a float-only `exp` method is insufficient. Third-party forward interpretation must not require exclusive method edits to `std` owners. The reverse transformation must preserve the coefficient/rule and residual dependencies needed for admitted higher-order composition. The required conformance demonstration is **forward-over-reverse Hessian-vector product**, not merely a stand-alone dual-number demo (tracked in #161). No public standard forward/JVP engine is required.

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

The shared [issue/PR review checklist](../std-issue-governance.md) is a non-normative shorthand for documenting this procedure without duplicating all governance boilerplate in every tracker. It does not alter the admissions or proof gates below.

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

### 10. Mathematical counterpart manifest and independent reference status (2026-11-01 integration proposal)

For each admitted public mathematical symbol, record its defining owner, exact mathematical denotation and equivalence, domain/hypotheses, structural-completeness requirements (#279), executable presentation and evidence status. Assign a mathematical counterpart class: **Lean core/Std**, **pinned mathlib**, **independent VastitasMath**, or **none with reviewed ADR exception**. For `std::structure` algorithms add an explicit **accepted-Core operational body + mandatory claim/evidence-status** class, and require a mathematical counterpart whenever an invariant/extensional property is claimed (e.g. `List.mergeSort` for stable sorting). Representation dependence is **not** a blanket `none` exception. A blank or `none` entry is not a way to bypass admission. Preserve source/model revision and actual-Core binding for any accepted conformance theorem.

The machine-readable manifest schema/CI and minimal `VastitasMath` are implementation obligations under #285/#386, not completed features of this ADR. `VastitasBridge` alone may depend on pinned mathlib; an Oracle may not. Independent Python/reference programs remain useful **tests**, never an additional mathematical proof authority. Lean `native_decide` introduces native-evaluation axioms and cannot supply a proof under the current allowlist; use kernel-checked reduction/proof terms instead.

The pure `std::category` Monad foundation must name its base category and separately admit strength/commutativity/graded laws where meaningful; linear/affine ownership does not inherit cartesian strength automatically (#199/#206/#207/#350). The privileged `std::monoidal::tensor` retains one generic identity but must resolve model-owned implementations through authorized bindings and checked evidence, never foreign import-side method mutation (#201/#223/#387).

This subsection records architecture and audit obligations only, not a wholesale reclassification of historical reference PRs or a claim of implemented conformance.

## Consequences, validation and migration

- A *thick* foundational `std` can cover algebra, topology/geometry, analysis, infinite-dimensional quantum mechanics and the mathematical formulation of equations, while a potentially infinite space of approximation algorithms remains in the ecosystem.
- The compiler need not know every mathematical object by name. It **does** need stable generic authority, indexed IR and checked evidence interfaces for admitted library contracts.
- The public `std` is not committed to universal solvers, general decidable equality, exact floating-point algebra or automatically differentiable singular/infinite-dimensional operators.
- **This ADR PR is documentary.** Its validation consists of consistency review against [the v0.3 design index](../design.md), #49/#60/#66/#67/#69/#71/#91/#92/#103/#104/#107/#159, and a negative-case/admission audit. It does not implement the exemplar algorithms, claim Lean theorems, or change the compiler/runtime.
- Implementation and executable acceptance, including exact algebra/representation, complex/symplectic geometry, functional/Hilbert/PDE reference examples, third-party AD rules, HVP, equivariant linalg, scalar profiles and optimizer regressions, are tracked in **[#160](https://github.com/MGYamada/Vastitas/issues/160)** and its child/existing issues.
- The historical Draft v0.3 transcription in `docs/design/` remains preserved. To the extent its provisional `§12.5` small-library wording conflicts with this approved charter, the ratified ADR is the later normative boundary **since PR #166 merged**. Concrete API designs still require their own decisions.

**Principle:** *Standardize the mathematical world and the trusted contracts connecting it; choose algorithms for realizing that world explicitly.*
