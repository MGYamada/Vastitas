# Vision and design status

[設計書の索引 / Design index](../design.md) · [出典 / References](history-references.md#18-mathematical-and-language-references)

> Historical design proposal: Draft v0.3, 26 October 2026 (JST). Original section numbering and qualifications are retained. This document does not assert current implementation or proof coverage; see the [repository README](../../README.md) for the implementation status.

<!-- draft-v0.3:preface:start -->
# Vastitas — A Language for Math 2.0 and Physics 2.0

*First-class geometry, executable mathematical meaning, and accountable physical modeling*

**Revision:** Draft v0.3 — dimension-graded quantities, bounded dispatch authority, declarative extension, and evidence invalidation  
**Date:** 26 October 2026 (JST)  
**Immediate predecessor:** Vastitas design draft v0.2, 26 October 2026  
**Earlier predecessor:** Marée initial design draft 0.1, updated 23 October 2026  
**Status:** Research-language design proposal; no implementation, formal verification, or empirical validation is claimed  
**Display name:** Vastitas  
**Proposed command:** `vastitas`

**Vastitas is a language for Math 2.0 and Physics 2.0.** It treats mathematical objects, morphisms, families, and their lawful transformations as programmable entities, while distinguishing mathematical meaning from numerical realization and physical evidence.

The mathematical foundation is algebraic geometry: ordinary `Scheme` and `CInfScheme` are complementary first-class settings, with module sheaves, generalized points, tensor products, and geometric constructions. A spectral computation can return a family with its operator action; a subspace can be a Grassmannian point; a reverse derivative can be a map between cotangent fibers. Coordinates and algorithms realize these objects without becoming their definitions.

The Physics 2.0 direction extends this premise: physical models should expose their geometry, dynamics, symmetries, observables, domains of validity, approximation choices, and comparison with evidence. Physical units are dimension-graded instances of the same monoidal discipline as line-valued geometry. Formal checking can validate consequences *within* a model. Neither a proof nor a numerical solver can, by itself, establish that nature follows the model.

The name *Vastitas* evokes a vast, unfamiliar landscape: a horizon explored through structure rather than a ready-made map. This is an image for research, not a claim that mathematical abstraction removes singularities, resolves empirical uncertainty, or supplies algorithms automatically.

## Contents

1. [Math 2.0, Physics 2.0, and design status](vision-status.md#1-math-20-physics-20-and-design-status)
2. [Two geometric settings](geometry.md#2-two-geometric-settings)
3. [First-class objects, points, and staging](geometry.md#3-first-class-objects-points-and-staging)
4. [Constructions, families, and base change](geometry.md#4-constructions-families-and-base-change)
5. [Module sheaves and Grassmannian points](geometry.md#5-module-sheaves-and-grassmannian-points)
6. [The common tensor product](tensor-resources-units.md#6-the-common-tensor-product)
7. [Ownership and tensor-network ports](tensor-resources-units.md#7-ownership-and-tensor-network-ports)
8. [Pure functions, independent lambdas, and dispatch](functions-dispatch.md#8-pure-functions-independent-lambdas-and-dispatch)
9. [Differentials and reverse differentiation](differentiation-spectral.md#9-differentials-and-reverse-differentiation)
10. [Eigen as spectral geometry](differentiation-spectral.md#10-eigen-as-spectral-geometry)
11. [SVD as geometry with a retained map](differentiation-spectral.md#11-svd-as-geometry-with-a-retained-map)
12. [Representations, numerical execution, and physical models](physics-compiler-verification.md#12-representations-numerical-execution-and-physical-models)
13. [Compiler architecture, verification, and AI](physics-compiler-verification.md#13-compiler-architecture-verification-and-ai)
14. [Initial implementation sequence](roadmap-acceptance.md#14-initial-implementation-sequence)
15. [Acceptance examples and diagnostics](roadmap-acceptance.md#15-acceptance-examples-and-diagnostics)
16. [Open design questions](roadmap-acceptance.md#16-open-design-questions)
17. [Version decisions and source record](history-references.md#17-version-decisions-and-source-record)
18. [Mathematical and language references](history-references.md#18-mathematical-and-language-references)

<!-- draft-v0.3:preface:end -->

<!-- draft-v0.3:1:start -->
## 1. Math 2.0, Physics 2.0, and design status

### 1.1 Math 2.0: mathematical objects as programs

The Math 2.0 thesis is that software can become a native medium for *constructing, transforming, and checking mathematical meaning*. A scheme, sheaf, morphism, tensor diagram, or spectral object should be available as an object of a program, rather than only as an informal explanation for an array algorithm.

The language separates a mathematical denotation from its finite presentation, executable realization, and proof or checking status. Equivalence of expressions is justified by admitted laws or explicit transport, not by coincidentally matching array shapes. A compiler may specialize away geometric abstractions only when their relevant obligations survive lowering.

Math 2.0 aspires to continuity with established mathematics: an old theorem does not become false because its proof is formalized, and exact objects retain their intended mathematical meaning. This is *semantic continuity*, not a promise that every historical proof can be translated automatically or that every existing program remains source-compatible.

### 1.2 Physics 2.0: executable theories under empirical constraint

The Physics 2.0 thesis is more radical. A physical theory can be developed as an explicit, executable network of geometric objects, states, dynamical laws, assumptions, approximations, and observables. Formal methods and AI-assisted construction can make larger theoretical structures tractable, including structures difficult to explore through an individual's intuition alone.

But a physical theory is not just a theorem. Its mathematical consistency, numerical correctness, and empirical adequacy are distinct questions. Vastitas should make those boundaries visible:

| Layer | Question it can answer | What it cannot establish alone |
| --- | --- | --- |
| Mathematical specification | Is the intended object or statement well defined under stated assumptions? | That the assumptions describe nature |
| Formal derivation | Does a conclusion follow from admitted axioms and verified rules? | That the axioms are physically adequate |
| Numerical realization | Was an ideal computation approximated under a stated precision and error policy? | That the ideal model predicts experiments |
| Physical model | Which regimes, scales, symmetries, and idealizations are claimed? | Validity outside those claims |
| Empirical comparison | How do predictions compare with identified observations and uncertainties? | A once-and-for-all proof of physical truth |

The possible discontinuity of Physics 2.0 is methodological: it need not preserve the legacy representation of theories as derivations, plots, and hand-assembled numerical pipelines. It must still respect reproducible evidence and the successful predictive constraints of prior physics. New mathematical foundations do not grant permission to ignore experiments.

### 1.3 An algebraic-geometric research language

Vastitas is intended for exact and differentiable mathematics, scientific computation, numerical linear algebra, tensor networks, and geometric physics. Initial executable targets are deliberately finite and comparatively small; mathematical objects need not be computationally materializable in every case.

The language takes responsibility for typed composition, geometric bases and endpoints, tensor wiring, resource lifetimes, and preservation of declared mathematical meaning. A physical-model layer will additionally track explicit assumptions, units or dimensions where supported, observable definitions, and numerical policies. The researcher remains responsible for choosing the physical model, meaningful observables, approximation and truncation schemes, validity regimes, and standards of experimental comparison.

Rust-like readable syntax, pure functional composition, exploratory numerical use, and a small core suitable for formal verification are design goals. Efficient lowering to native kernels is a requirement to investigate and measure, not a theorem supplied by the syntax or geometry. The core is *closure-free* and avoids hidden runtime capture; it need not expose every proof object in everyday numerical code.

### 1.4 Commitments and maturity

This draft distinguishes three levels of commitment:

| Level | Meaning |
| --- | --- |
| Established direction | A choice carried forward from the design discussions, including the first-class geometric foundation and the common tensor product. |
| Proposed mechanism | A concrete way to realize that direction, introduced here for review and prototyping. |
| Deferred question | A boundary that needs a separate decision or implementation study. |

Statements using “must” describe requirements of this proposed design. They do not assert that a compiler already satisfies them. All code blocks are illustrative pseudocode. Constructor names, grammar, namespace spelling, and dependent-type elaboration are provisional.

The established direction is:

- Math 2.0 and Physics 2.0 are the two public purposes of Vastitas, with separate mathematical, numerical, and empirical notions of acceptance.
- `Scheme` and `CInfScheme` are first-class geometric objects.
- `Affine`, `Projective`, `Grassmannian`, zero loci, and fiber products are geometric constructions.
- Generic `Space` or `SubSpace` is not the root of the public geometric model.
- Morphisms, module sheaves, families, and base change have explicit meaning.
- A common typed `⊗` connects tensor values, linear maps, and tensor-network diagrams.
- Algebraic duality does not silently conjugate complex coefficients.
- Pure mathematical semantics coexist with explicit resources and controlled local mutation.
- First-class functions are closure-free; anonymous functions have explicit runtime dependencies.
- Multiple dispatch is resolved statically within an identified supported subset, initially including finite nominal types and finite static capability atoms.
- Whole generic functions have linear construction ownership; declared extension deltas compose without inspecting construction history, and a borrow's approved impact region bounds which final calls its methods may win.
- Unresolved coherence and impact obligations follow moves and borrows until checked completion; the immutable build environment identifies what has been checked.
- The public numerical AD core is reverse-oriented: `pullback`, `grad`, and `CoTangent`.
- Spectral objects retain multiplicity and operator action; a selected eigenvector list is not their definition.
- Physical theories are composed from typed geometric and dynamical structure; dimensions form a graded monoidal profile, while their assumptions, scale, and observed consequences must not be conflated with proofs.
- Formal derivations and empirical comparisons have different monotonicity properties; evidence records depend on identified model, realization, and dataset revisions.
- AI-generated proposals are untrusted input to the same semantic, resource, and verification boundaries as human-written code.

The detailed `Model`/`Theory` surface, the representation and syntax of the dimension-grading profile, observational data interface, and empirical-validation APIs in Sections 12–16 are **proposed mechanisms**, not established executable features.

Vastitas is distinct from Qleisli. Vastitas is a mathematical and scientific language running on classical computational resources; it can describe and simulate quantum physical models, but it does not thereby import quantum no-cloning restrictions, quantum effects, release plans, or proof guarantees from Qleisli. A future explicit bridge between them may be useful, but no shared runtime or verified interoperability is specified here.

<!-- draft-v0.3:1:end -->
