# Version history and source references

[設計書の索引 / Design index](../design.md) · [出典 / References](history-references.md#18-mathematical-and-language-references)

> Historical design proposal: Draft v0.3, 26 October 2026 (JST). Original section numbering and qualifications are retained. This document does not assert current implementation or proof coverage; see the [repository README](../../README.md) for the implementation status.

<!-- draft-v0.3:17:start -->
## 17. Version decisions and source record

### 17.1 Lineage and the Vastitas name

The research-language design was first discussed under *Kleisli* and then *Sinthome*. The decision to make ordinary `Scheme` and `CInfScheme` first-class, rather than treating schemes as hidden justifications for numerical functions, led to the name *Marée* (ASCII *Maree*). Its initial design draft 0.1 was updated on 23 October 2026.

**Draft v0.2 adopts the name Vastitas and the defining subtitle “A Language for Math 2.0 and Physics 2.0.”** The rising-sea image associated with Marée is part of the project's conceptual history; the Vastitas name turns toward the image of a vast landscape and an unfamiliar horizon. This is a change in identity and scope, not a repudiation of the algebraic-geometric design.

The v0.2 document was a successor draft, not an in-place assertion that the 23 October document already contained the new Physics 2.0 layer. The present v0.3 draft retains that foundation and sharpens the dimensions, dispatch, and evidence contracts.

### 17.2 Technical design carried forward from v0.1

The mathematical architecture remains intact:

- First-class ordinary and smooth schemes, generalized points, sheaves, Grassmannian quotients, and base change.
- The common tensor-product contract and explicit distinction between algebraic duality, conjugation, and metric adjoint.
- Linear tensor-network occurrence ports separated from affine numerical-storage ownership.
- Closure-free independent functions, static multiple dispatch, and linearly owned whole-function construction with coherence obligations.
- Reverse-oriented AD, point-dependent cotangents, and metric-aware gradients.
- Structural types and local checked operations rather than a universal regularity ledger.
- Spectral schemes with module action, separated-cluster outputs, and retained SVD connecting maps.
- A small standard library, modular numerical backends, and honest numerical boundaries.

In particular, Section 8.3 retains the function-ownership revision of 23 October 2026. Draft v0.3 extends its finite nominal checking kernel to static capability atoms and adds authorized-impact and declarative-composition conditions. These are proposed executable starting points; their conditional lemmas are not proofs of full-language soundness.

Sections 2.4 and 10.3 retain the mathematical analysis from the predecessor: the left adjoint for real smooth realization, disappearance of non-real points, the hyperbolic polynomial comparison over smooth manifolds, and the limitation of the real two-equation model at complex multiple roots. These arguments are written in the draft; they have **not** been claimed to be machine-checked.

### 17.3 New decisions in v0.2

- Math 2.0 and Physics 2.0 replace “an algebraic-geometric language for scientific computation” as the public project thesis.
- The conceptual difference between semantic continuity in mathematics and possible methodological discontinuity in physics is made explicit (Section 1).
- Physical parameter spaces, invariant observations, response hypotheses, and truncation or singular-limit policies are named as physics-facing obligations (Sections 4–11).
- A proposed physical-model layer separates mathematical objects and physical interpretation, ideal observables and numerical predictions, and predictions and empirical evidence (Section 12).
- Verification distinguishes formal consequence, numerical guarantee, statistical support, and empirical adequacy; AI-generated artifacts must cross the same checking boundaries as other inputs (Section 13).
- The implementation plan, acceptance examples, and open questions now include a small Physics 2.0 vertical slice (Sections 14–16).

These v0.2 additions define **interfaces and verification obligations to investigate**, not already implemented language features or a comprehensive physical ontology.

### 17.4 New decisions in v0.3

- Remove the now-redundant “ASCII name” header field; *Vastitas* needs no transliteration from an accented display name.
- Define physical dimensions as a $\mathbb Z^k$- or $\mathbb Q^k$-graded symmetric monoidal profile of oriented quantity lines (Section 6.6), reusing the line-valued discipline of Plücker data rather than introducing an unrelated units mechanism. Unit frames are trivializations; Buckingham invariants are dimensionless combinations; natural units are tracked line isomorphisms; Celsius-like affine readings are additive torsors, not ordinary quantity vectors.
- Restrict the implicit Euclidean metric to settings with a dimensionally valid declaration. Mixed-unit parameter coordinates without an appropriate metric must yield a missing-metric diagnostic for `grad` (Sections 9.3 and 15).
- Preserve whole-function linear ownership but bind contributor impact through an owner-approved region $R_X$ and a final winning-footprint inclusion test. This blocks coherent yet unauthorized method replacement without resurrecting intersection-by-intersection ownership (Section 8.3).
- Enlarge the finite dispatch kernel from nominal types to the product of nominal subtype order and a finite static capability-set order; keep erased, open-world, or dynamic capability selection outside the admitted fragment (Section 8.3.5).
- Make ordinary extensions **declarative deltas** whose compatible union is associative, commutative, and idempotent. Separate explicitly ordered, state-reading integration operations and record them in the build environment (Section 8.3.6). Pure assembly confluence derives from the delta algebra, while linearity continues to track edit authority and responsibility.
- Keep formal, numerical, statistical, and empirical support conceptually distinct while recognizing their different monotonicity. Key empirical comparison records by versioned model, realization-policy, and dataset identities and invalidate through the same dependency graph as dispatch certificates, with **different** per-record revalidation rules (Sections 8.3.6 and 13.4).

All these mechanisms remain **design proposals**. No implementation, proof, or experimental validation is asserted by the v0.3 revision.

### 17.5 Predecessor documents and attribution

The specific discussions and predecessor documents underlying draft 0.1 include:

- *Kleisli-initial-design-2026-10-17(1).md*, inspected version 2 in the predecessor draft.
- *Kleisli-design-2026-10-17.md*, inspected version 1 in the predecessor draft.
- *Kleisli-integrated-design-2026-10-18.md*, the consolidated proposal.
- The subsequent discussions establishing first-class `CInfScheme`, adding ordinary `Scheme`, and distinguishing tensor ownership.
- *Maree-initial-design-draft-0.1-2026-10-23.md*, the direct source of the v0.2 revision.
- *Vastitas-language-design-draft-v0.2-2026-10-26.md*, the immediate predecessor of this v0.3 revision.

Where earlier drafts differ on public object names or demote schemes to background semantics, the first-class geometric architecture in this document takes precedence. The v0.2 thesis added physical interpretation and evidence boundaries on top of that architecture; v0.3 adds the specified graded, dispatch, and version-dependency mechanisms.

The specific type families, constructor spellings, staging scheme, proof boundaries, and implementation sequence remain proposals. No implementation, numerical benchmark, Lean formalization, or experimental result is claimed; nor is historical uniqueness asserted.

<!-- draft-v0.3:17:end -->

<!-- draft-v0.3:18:start -->
## 18. Mathematical and language references

These references ground the mathematical vocabulary and the comparison with existing dispatch systems. They do not constitute a specification or verification of Vastitas.

- **[J1]** Dominic Joyce, *Algebraic Geometry over C-infinity-rings*, arXiv:1001.0023, version 7. [Author's paper](https://arxiv.org/abs/1001.0023).
- **[J2]** Dominic Joyce, *An introduction to C-infinity schemes and C-infinity algebraic geometry*, arXiv:1104.4951, version 2. In particular, the discussion of smooth-ring coproducts, modules, and cotangent objects. [Author's survey](https://arxiv.org/abs/1104.4951).
- **[S1]** The Stacks Project, Tag 01HX, *The category of affine schemes*. [Reference](https://stacks.math.columbia.edu/tag/01HX).
- **[S2]** The Stacks Project, Tag 01JO, *Fibre products of schemes*. [Reference](https://stacks.math.columbia.edu/tag/01JO).
- **[S3]** The Stacks Project, Tag 01UM, *Sheaf of differentials of a morphism*. [Reference](https://stacks.math.columbia.edu/tag/01UM).
- **[S4]** The Stacks Project, Tag 089R, *Grassmannians*. Its displayed rank convention differs from the explicit quotient-rank convention used here. [Reference](https://stacks.math.columbia.edu/tag/089R).
- **[BM1]** Jean Cerqueira Berni and Hugo Luiz Mariano, *Topics on Smooth Commutative Algebra*, arXiv:1904.02725v2, Section 2, especially Remark 2.3 for the forgetful functor to real algebras. [Paper](https://arxiv.org/abs/1904.02725).
- **[T1]** Vincent Thilliez, *Estimates for Weierstrass division in ultradifferentiable classes*, arXiv:1511.08484v2, Introduction. The smooth Malgrange–Mather division statement recalled there is the input to the proof of Section 10.3.2; the hyperbolic comparison and globalization are derived in this document. [Paper](https://arxiv.org/html/1511.08484v2).
- **[JL1]** Julia documentation, *Julia Functions* and *Modules*, accessed 23 October 2026. Generic-function identity and cross-module method extension. [Functions](https://docs.julialang.org/en/v1/devdocs/functions/); [Modules](https://docs.julialang.org/en/v1/manual/modules/).
- **[JL2]** Julia documentation, *Methods*, especially *Method Ambiguities*, accessed 23 October 2026. [Reference](https://docs.julialang.org/en/v1/manual/methods/).
- **[JL3]** Julia documentation, *The World Age mechanism*, accessed 23 October 2026. [Reference](https://docs.julialang.org/en/v1/manual/worldage/).
- **[MC1]** Todd Millstein and Craig Chambers, *Modular Statically Typed Multimethods*, ECOOP 1999, pp. 279–303; especially the extension-module approach in System E. Its language and restrictions differ from this proposal. [Authors' paper](https://web.cs.ucla.edu/~todd/research/ecoop99.pdf).
- **[R1]** Rust RFC 1210, *Impl specialization*, especially *Interaction with lifetimes*. Used for the erasure issue, not as a claim about the current stabilization status of Rust specialization. [RFC](https://rust-lang.github.io/rfcs/1210-impl-specialization.html).
- **[U1]** Josef Janyška, Marco Modugno, and Raffaele Vitolo, *An Algebraic Approach to Physical Scales*, *Acta Applicandae Mathematicae* **110** (2010), 1249–1276. A mathematical treatment of positive scales and rational powers; Section 6.6 proposes Vastitas's own graded-interface interpretation. [Authors' manuscript](https://poincare.unile.it/vitolo/vitolo_files/publications/journals/23a_scales.pdf); [DOI](https://doi.org/10.1007/s10440-009-9505-6).
- **[U2]** Bureau International des Poids et Mesures, *The International System of Units (SI Brochure)*, 9th edition, version 4.01 (2026), especially the kelvin / Celsius temperature discussion. [Official brochure](https://www.bipm.org/documents/20126/41483022/SI-Brochure-9-EN.pdf).




<!-- draft-v0.3:18:end -->
