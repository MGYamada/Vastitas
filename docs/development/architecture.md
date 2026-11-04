# Compiler architecture

| Directory | Responsibility | Dependencies |
| --- | --- | --- |
| `src/` | Rust CLI, parser, lexical resolution, versioned IR | Rust dependencies in `Cargo.lock` |
| `lean-kernel/` | Independent semantic checking, hygienic code generation, minimal runtime | Lean distribution only; no mathlib |
| `lean/` | Proofs about the actual kernel definitions | Local kernel and Lean distribution only; no mathlib |
| `lean-bridge/` | Separately built mathematical foundations for future correspondence proofs | Pinned Lean and Mathlib; no compiler/runtime dependency |
| `stdlib/src/` | Standard library written in `.vast` | Explicitly included `.vast` sources |

The bridge contains the [Daleckii–Krein theorem](../daleckii-krein.md), an important
foundation for future spectral differentiation. It proves the real Fréchet
derivative of Mathlib's functional calculus at finite-spectrum self-adjoint
elements, including Hermitian matrices with repeated eigenvalues. Its separate
build, axiom audit and official kernel replay establish this mathematical result;
connecting it to a `.vast` AD implementation remains future work.

Ordinary compilation and generated programs do not call the proof oracle.
On the retained legacy Core path, the oracle proves Stage 0 checker soundness, source-to-core
correspondence, terminating typed evaluation, and runtime endpoint preservation.
It also proves the finite dispatch checker's unique selection, coverage, and
declaration-order invariance, and connects the retained Stage 1b checker's exact
lowered result to that proved core. Independent capture and static function
signature audits are connected to actual acceptance. Protocol-3 owner uniqueness,
reference/visibility and method-authority audits connect the namespace path to
the same core theorems. Protocols 5/6 also audit grant origins, exclusive loan transitions, complete contribution bodies and final winning footprints; protocol 6 additionally audits nested delegation and current-owner histories. Their exact assembled surfaces enter that same checker. Rust parsing, JSON decoding, full Stage 1
source rewriting correspondence, native code-generation equivalence, and a
full mathematical model of schemes remain outside those claims. The precise
[proof boundary](../verification.md) is part of the implementation contract.

The internal declaration-driven source adapters now compose independent
functions, finite scalar dispatch and edit-authority assemblies, including
applied and unapplied contribution bodies. [Public protocol 7](../indexed-source.md)
connects the Rust declaration/body syntax to that same combined checker and
returned Core. Legacy geometry syntax in protocols 7–9 uses the library’s explicit,
independently checked compatibility export. `IndexedProgramSafety` proves finite
typed evaluation for all functions and main in the exact returned Core, including
dependent calls and package openings. Finite geometry primitive results agree
with the retained runtime after erasure. Full source operational correspondence
and native refinement remain unproved. See
[indexed declarations](../indexed-source.md#indexed-declarations).

The [geometry standard library](https://github.com/MGYamada/Vastitas/blob/main/stdlib/src/geometry/README.md) exposes
`std::geometry::scheme` and `std::geometry::smooth` for the existing affine
descriptors, nominal points, morphisms and existential packages. Use the
`stdlib` dependency entrypoint for geometry and arithmetic together. Original
legacy geometry clients use the same declaration identities in that package
closure; the temporary `stdlib/indexed` entrypoint has been removed.
The new declarations use the same protocol-7 checker as application declarations,
without privileges from geometric names. General scheme/manifold mathematics,
new geometric constructions and the rest of #211 remain future work.
