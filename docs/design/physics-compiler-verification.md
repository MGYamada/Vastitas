# Physical models, compilation, and verification

[Design index](../design.md) · [References](history-references.md#18-mathematical-and-language-references)

> Historical design proposal: Draft v0.3, 26 October 2026 (JST). Original section numbering and qualifications are retained. This document does not assert current implementation or proof coverage; see the [repository README](../../README.md) for the implementation status.

<!-- draft-v0.3:12:start -->
## 12. Representations, numerical execution, and physical models

### 12.1 Meaning, presentation, and realization

Vastitas separates three responsibilities:

| Layer | Responsibility |
| --- | --- |
| Mathematical meaning | Object, morphism, family, tensor operation, or observation |
| Finite presentation | Equations, charts, module generators, maps, and construction descriptors |
| Numerical realization | Coordinates, buffers, precision, backend kernels, and error policy |

A finite presentation is not necessarily an efficient numerical representation. A numerical representation is not the definition of the object.

A geometric value can have several realizations. Conversion must preserve the relevant meaning and make materialization or transfer costs visible where they matter.

### 12.2 Exact scalars and floating-point data

IEEE floating-point arithmetic is not an exact field and must not instantiate the exact ring laws of `Scheme`.

Finite floating-point inputs can be interpreted as exact represented real or complex values at a specified boundary. Numerical operations then approximate the ideal computation under a declared policy. Overflow, nonfinite inputs, rounding, and solver residuals remain numerical concerns.

AD targets the ideal real or complex denotation, or an explicitly selected backward convention. It does not claim a classical derivative of the discrete map on machine bit patterns.

Estimated rank and gap checks must be described as estimates unless a backend supplies certified bounds. Tolerance-based grouping is not proof of exact degeneracy.

### 12.3 Geometry-aware numerical wrappers

A geometric object may be implemented with private frames, factorizations, sparse data, or implicit linear operators. Its public endpoint identity and available operations must survive representation changes.

Array convenience types remain useful. They describe storage-shaped numerical values or coordinate realizations, with a clear association to the relevant module or geometric object.

CPU/GPU placement belongs to execution resources and storage ownership. It does not require a different logical geometric type. Transfers can still have significant costs and must not be hidden behind a promise of free coercion.

### 12.4 Lazy descriptors and generative handles

A spectral descriptor retains immutable input and semantic parameters. Its construction need not generate a fresh public bundle identity or call a solver.

A checked cluster observation can package newly scoped endpoints. Maps from that package agree on those endpoints. Two independently returned handles are not identified merely because they have the same dimension or share cached factors.

Generative identities must remain abstract: fresh names cannot become numerical coordinates or observable global counters. AD replay and checkpointing preserve or explicitly reconstruct endpoint associations without differentiating identity tokens.

Operational caches may change cost. They must not change semantic results or the requested derivative policy.

### 12.5 A small standard library

The initial standard library should provide foundational objects, scalar and module interfaces, typed tensor operations, basic geometric constructions, and the reverse AD interface.

Numerical solvers, backend adapters, and scientific applications should be modular. An admitted library operation supplies:

1. Typed inputs, outputs, and structural capabilities.
2. Its mathematical meaning and preconditions.
3. Its implementation and numerical failure behavior.
4. A backward implementation when available.
5. The laws needed by compiler rewrites or formal verification.

There is no requirement that every scalar primitive allocate a scheme or construct a sheaf record. First-class geometry is available to programs that use it; routine numerical expressions can elaborate through established objects and primitive rules.

### 12.6 A physical model is a structured claim

The mathematical semantics of a physical model are built from objects already present in Vastitas: parameter spaces, states or state families, maps, operators, bundles, tensor products, and observables. The Physics 2.0 layer associates these with **physical interpretation and explicit assumptions**.

A proposed model descriptor has at least the following conceptual parts. This is not a fixed universal `Model` constructor or a claim that every physical theory has a finite-state Hamiltonian presentation.

| Part | Meaning | Example of an obligation |
| --- | --- | --- |
| Parameter geometry | Where couplings, sources, positions, or time parameters live | Every parameter-dependent family has a declared base |
| States and fields | Which configurations or state spaces a theory admits | Operator endpoints agree with the specified state object |
| Laws and dynamics | Constraints, evolutions, actions, or generators | Admitted operations preserve the stated structure |
| Symmetry and gauge | Group actions, equivariance, changes of presentation | Intrinsic observables are independent of unobservable frame choices |
| Observables | Functions or correspondences assigned physical meaning | Units, domains, and source conventions are consistent |
| Assumptions and regime | Finite size, equilibrium, boundary conditions, scales, idealizations | No claim silently escapes its domain |
| Realization policy | Approximation, truncation, solver, precision, error model | Results identify which ideal computation they approximate |

The fields in this table may be represented by a family of interoperable types and traits, not one enormous record. A physically motivated constraint need not be decidable by the compiler; unsupported checks must be visible as assumptions or obligations, never silently counted as proofs.

One intended style, entirely provisional, is:

~~~text
let B = Affine(CInfReal, 2);
let H = hermitian_family(B, [[x, y], [y, -x]]);

let model = physical_model(
    parameters = B,
    states = domain_bundle(H),
    law = hamiltonian(H),
    assumptions = [closed_system(), finite_size(2)]
);

let invariant = observable(model, fn(H) { trace(H * H) });
let ideal_prediction = predict(model, invariant);
let computed = realize(ideal_prediction, policy = declared_solver_policy);
~~~

This code sketches the separation of an intrinsic observation, a physical interpretation, and a numerical realization. It does not define the semantics of every Hamiltonian, measurement, or solver, nor a final grammar for these calls. In particular, `finite_size(2)` is an explicit finite-system assumption, not a statement about a thermodynamic limit.

### 12.7 Units, domains, approximations, and limits

Physical quantities need additional structure beyond scalar type and array shape. Section 6.6 defines their core as a $\mathbb Z^k$- or $\mathbb Q^k$-graded monoidal profile of oriented quantity lines and their sections. The profile rejects unsupported addition of incompatible degrees, carries line-valued results through `⊗`, and makes changes of unit frames explicit. Natural-unit declarations are named line isomorphisms and degree relations, not silent coercions to dimensionless scalars. Affine measurements, including Celsius temperature readings, are modeled as additive torsors over dimension lines; their points and differences obey different arithmetic. The remaining questions are surface ergonomics, affine conversions, and integration with supported realizations, **not** the invention of an unrelated units type system.

The following boundaries are intentionally distinct:

- **Mathematical domain:** where the morphism or observation is defined.
- **Differentiability domain:** where the requested classical derivative exists and the admitted backward rule is correct.
- **Numerical domain:** where an algorithm can produce a result meeting a declared error or convergence requirement.
- **Physical validity regime:** where the model's approximations, state preparation, and empirical interpretation are claimed to apply.

None of these domains may silently stand in for the others. A solver can converge to a value outside the intended physics regime. A model may be physically plausible even when its current numerical realization fails. A mathematically exact finite-size identity does not automatically hold after a singular limit.

An approximation is a relation between an ideal object and a chosen realization or effective model, equipped with whatever estimate or validation is actually available. Variational truncation, perturbative order, regularization, lattice spacing, system size, statistical sampling, and extrapolation all need explicit policies. Not all approximations admit certified error bounds; the language must distinguish estimated, tested, and proved guarantees.

Limits such as continuum, infinite volume, zero temperature, and long time may fail to commute. The language should preserve their order as part of an explicit construction when a physical claim depends on it, rather than normalizing them as interchangeable numerical parameters.

### 12.8 Predicted observables and empirical evidence

An *ideal observable* is a mathematical object associated with a specified model. A *computed prediction* realizes it numerically. A *measurement* is external evidence with provenance, units, calibration, uncertainty, and experimental conditions. A *comparison* aligns the three under documented interpretation and statistical assumptions. Its minimally required dependency key is $(\text{model identity},\text{realization policy identity},\text{dataset identity})$; calibrated datasets and statistical comparison policies also carry versioned identities within this dependency closure. Changing any such input invalidates the current comparison record until recomputation or a justified reuse check (Section 13.4).

The proposed public model should not let an array of measurements impersonate an exact `Section` or `Morphism` merely because it has compatible dimensions. Similarly, a verified theorem about the spectrum of a model cannot be labeled an experimentally verified spectrum.

Empirical workflows require uncertainty propagation, parameter inference, statistical tests, and reproducibility. These are major library and research-design problems, not automatic consequences of `Scheme` or `CInfScheme`. The v0.2 draft fixes the separation of responsibilities, not an inference engine or a canonical experimental-data format.

### 12.9 Mathematical physics without pretending to have a quantum runtime

Classical mechanics, smooth geometry, lattice Hamiltonians, topological phases, field-theoretic structures, and tensor networks can all motivate Vastitas libraries. Their common substrate is typed mathematical meaning with declared capabilities, not one mandatory state representation.

For quantum many-body *simulation*, Vastitas may manipulate complex modules, operators, tensor categories, wavefunctions, and numerical approximations using classical hardware. Executing a quantum program with its own ownership and physical-realizability contract belongs to a separate concern such as Qleisli. An eventual bridge must state what is translated, simulated, approximated, or proved; shared vocabulary alone is insufficient.

<!-- draft-v0.3:12:end -->

<!-- draft-v0.3:13:start -->
## 13. Compiler architecture, verification, and AI

### 13.1 Proposed compilation pipeline

The proposed pipeline is:

1. Parse and elaborate source, including generics, geometric indices, graded dimension lines, finite static capabilities, explicit dependencies, and declared mathematical or physical-model contracts.
2. Merge compatible declarative method deltas under whole-function linear ownership and scoped impact grants; record any ordered integration actions; discharge coherence, coverage, noninterference, and dependent call obligations; seal the identified method environment and check resource and endpoint compatibility.
3. Construct a typed semantic IR retaining geometric and monoidal information.
4. Apply admitted structural rewrites and the reverse transformation.
5. Choose finite representations, materializations, and numerical algorithms.
6. Plan storage, residual retention, scheduling, and device transfers.
7. Lower to executable kernels and target code.

Specialization may interleave with these stages. No stage may erase information still needed by a later check.

The IR should retain:

- Geometric setting and base.
- Object and endpoint identities.
- Module structure, tensor profile, static capability evidence, dimension grades, and line or affine-unit identifications.
- Point and cotangent basepoint associations.
- Function and method identities, declarative contribution records, approved impact regions, any ordered integration plan, the finalized environment and dependency certificates, and targets or explicit control flow selecting known targets.
- Buffer lifetimes and linear network ports.
- Observation domains, derivative policies, and numerical implementation choices where relevant.
- Physical-model assumptions, interpretation boundaries, graded units and metric scales where enabled, and identities of explicit approximation, limiting, and evidence-comparison operations.

“Retain” does not mean attaching a universal proof ledger to every expression. Static metadata, construction invariants, primitive specifications, and scoped runtime records have different jobs.

### 13.2 Verification targets

| Target | Intended statement |
| --- | --- |
| Type and endpoint preservation | Accepted transformations preserve the indexed interfaces used by the program |
| Function construction safety | Whole-function edit authority is exclusive, and moves and borrow returns preserve outstanding obligations |
| Declarative extension confluence | Compatible history-free library deltas have the same union and sealing result regardless of merge order; ordered integration actions are separately recorded |
| Dispatch coherence, coverage, and impact | Accepted calls in a finalized environment have a unique most-specific applicable target, independent of erased lifetimes and generative identities, and each contributed winner lies within its approved region |
| Resource safety | Execution respects buffer access, lifetimes, residual validity, and linear port use |
| Geometric construction correctness | Admitted constructors implement their stated objects and maps |
| Structural rewrite correctness | Rewrites preserve the selected monoidal and geometric laws |
| Reverse correctness | On the supported primitive-regular domains, generated code computes cotangent pullback |
| Dimension-graded operation correctness | Addition, tensor products, unit conversions, and any supplied metric respect their declared dimensions; mixed-unit `grad` cannot silently use an invalid Euclidean default |
| Numerical refinement | A numerical implementation approximates its specified ideal observation under stated hypotheses |
| Physical-model well-formedness | Model components share consistent bases, state objects, declared units, hypotheses, and observable interfaces |
| Claim provenance and invalidation | A reported result identifies its kind of support and the versioned dependencies that must be rechecked when its evidence inputs change |

These are separate obligations. A type-correct floating-point kernel is not automatically accurate. A correct exact construction does not imply a stable numerical algorithm. A valid primal implementation does not automatically provide higher-order AD.

Lean is a candidate for reference semantics and selected proofs, following the project's verification direction. This draft does not fix the full proof architecture or claim existing coverage.

### 13.3 Trust boundaries

A foreign kernel, custom derivative, or unchecked geometric constructor must have an identifiable admission boundary. Its signature alone is not a proof of its laws.

Proofs, reviewed implementations, and numerical checks support different claims. The implementation must not label a heuristic estimate as a formal certificate.

The target is a small comprehensible core with explicit extension points. Automatic proof search for arbitrary geometry, arbitrary smooth equality, and arbitrary program termination is outside the initial compiler.

### 13.4 Verification must not erase epistemic boundaries

Vastitas needs at least four **distinct descriptions of support**, implemented through immutable proof or evidence records, certificates, and a controlled reporting API—not necessarily as four static types of the claimed mathematical object:

1. **Formally established:** a statement proved from identified axioms, trusted definitions, and admitted rules in a specified theory and environment.
2. **Numerically certified or estimated:** a result accompanied by the numerical algorithm, precision and error policy, and a certificate or estimate whose strength is explicitly stated.
3. **Statistically supported:** a conclusion depending on an identified dataset and statistical model, assumptions, and uncertainties.
4. **Empirically supported:** a physically interpreted comparison with observations, including the experimental context and limits of the claim.

These descriptions are not an ordered ladder in which a later label automatically includes an earlier one. They also have **different monotonicity laws**. Formal entailment is monotone under the *addition* of axioms while the language, definitions, inference rules, and meanings of the statements remain fixed (with the usual proviso that new premises may undermine the intended consistency or applicability of the theory). Changing a definition, trust assumption, or proof environment is not such a mere addition and requires proof rechecking. Empirical support is generally **nonmonotone**: additional measurements, recalibration, a revised statistical model, or a changed validity regime can strengthen, weaken, or overturn it. Numerical estimates and statistical conclusions likewise require their own policy-specific validity checks. A rigorously proved theorem may have no experimentally useful content; a successful prediction need not have a formalized mathematical proof.

The reference mechanism is the **same versioned dependency tracking** used for dispatch certificates in Section 8.3.6, with different validation rules per record kind. In particular, a physical comparison has a key

$$
\operatorname{ComparisonKey}
=\bigl(\operatorname{ModelId},\operatorname{RealizationPolicyId},\operatorname{DatasetId}\bigr),
$$

where each identity denotes a versioned artifact and its transitive dependencies: model definitions and interpretation, solver/precision/approximation choices, measurement calibration and uncertainty metadata. This triple is the **required dependency tuple**, not a globally unique identifier for every comparison: the target observable and comparison protocol must also have explicit identities (either included in the model/realization specifications or attached to the record). Statistical assumptions are likewise identified dependencies. A change to **any** of these identities marks the comparison **stale**, not false and not automatically still supported; its status must be recomputed or justified by an appropriate reuse certificate. A proof certificate, by contrast, can often be reused under a genuine extension of fixed axioms when its exact dependencies remain valid. Both mechanisms can share a dependency graph without confusing formal validity with defeasible evidence.

It follows that compiler acceptance of a well-typed model should certify only the checks actually discharged. It must not return a blanket `PhysicalTruth` witness or bake a mutable state of empirical support into an immutable mathematical type. A report states its identified premises and whether each relevant record is current, stale, estimated, or certified under its **own** validation rules; user-facing tools must not silently promote one kind of support to another.

### 13.5 AI as proposer; specifications and checkers as boundaries

Math 2.0 and Physics 2.0 assume that humans and AI systems will both construct programs, search for conjectures, choose representations, and propose reductions or new models. Vastitas should make that collaboration productive without making the origin of a program its justification.

For any generated artifact, the proposed acceptance path is:

1. Construct source, a semantic object, or a candidate proof.
2. Elaborate against explicit geometric, type, resource, and model contracts.
3. Check admitted laws or independently verify supplied proof certificates where the formal system supports them.
4. Lower through semantics-preserving transformations; assess numerical realizations with their actual guarantees.
5. Where the claim concerns nature, compare model predictions with relevant observations and physical assumptions in an independently accountable workflow.

An AI output may satisfy step 2 and fail step 3; it may pass steps 2–4 and still be physically wrong. A convincing informal explanation cannot replace an unresolved proof obligation, and a plausible numerical plot cannot replace an experimental comparison.

An eventual machine-checked reference semantics (Lean is a candidate) should distinguish the **trusted kernel**, verified constructions, admitted external axioms, foreign-code assumptions, and empirical inputs. The exact proof-language integration and the fraction of the standard library proved in an initial release remain open. Vastitas inherits neither Qleisli's three-theorem acceptance gate nor any already-completed verification.

<!-- draft-v0.3:13:end -->
