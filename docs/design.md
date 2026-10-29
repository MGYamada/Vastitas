<a id="vastitas-言語設計"></a>

# Vastitas language design

**Current normative standard-library boundary:** [ADR 0001 — Mathematics-first standard-library admission and trust boundary](adr/0001-mathematics-first-stdlib.md). The v0.3 draft linked below is preserved as a historical proposal; normative policy and implementation status are separate. Track implementation in [#160](https://github.com/MGYamada/Vastitas/issues/160).

**Fast like C is the highest-priority performance and architecture goal.** The current
[revised Chapter 7 — Storage, ownership, and residual retention](storage-ownership.md)
defines layout, aliasing, resource transitions, allocation and copy costs, and
acceptance criteria based on comparison with C. Use the revised chapter for future
implementation decisions while preserving the original Chapter 7. Adopting a design
is separate from recording implementation, proofs, or achieved performance.

Vastitas aims to treat mathematical objects as first-class values while distinguishing
mathematical meaning, executable representations, and physical evidence. Ordinary
`Scheme` and smooth `CInfScheme` are parallel geometric settings, retaining explicit
bases, object identities, and morphism endpoints.

This index organizes the design draft v0.3, dated 26 October 2026, by topic. The split
documents retain all 18 original sections, equations, assumptions, qualifications,
acceptance examples, and references. Section numbers are unchanged; references such
as “Section 8.3” refer to the original numbering. The split changed only the original
table-of-contents destinations and added navigation outside the preserved text.

<a id="読み方"></a>

## Reading guide

| Topic | Original sections | Contents |
| --- | --- | --- |
| [Vision and design status](design/vision-status.md) | Preface, 1 | Math 2.0 / Physics 2.0; established directions, proposals, and open questions |
| [Geometric settings, objects, families, and sheaves](design/geometry.md) | 2–5 | Ordinary/smooth schemes, generalized points, existential packages, base change, Grassmannians, and line-valued Plücker data |
| [Tensors, dimensions, and resources](design/tensor-resources-units.md) | 6–7 | The common `⊗`, monoidal structure, units and dimensions, storage ownership, and linear ports |
| [Pure functions and static dispatch](design/functions-dispatch.md) | 8 | No implicit capture, whole-function edit authority, declarative differences, the finite checking kernel, and permitted footprints |
| [Reverse differentiation and spectral geometry](design/differentiation-spectral.md) | 9–11 | Cotangent spaces at a base point, metric-dependent `grad`, eigenvalue multiplicity and action, Hermitian clusters, and SVD retaining the connecting map |
| [Physical models, compiler, and verification](design/physics-compiler-verification.md) | 12–13 | Meaning versus representation, numerical realization, physical-model assumptions, IR, trust boundaries, and evidence dependencies/invalidation |
| [Implementation stages, acceptance, and open questions](design/roadmap-acceptance.md) | 14–16 | Completion criteria by stage, accepted and rejected examples, and future research/implementation questions |
| [Design history and references](design/history-references.md) | 17–18 | Decisions from v0.1 to v0.3, earlier drafts, and mathematical/language sources |

<a id="実装との関係"></a>

## Relationship to the implementation

Code in the draft is pseudocode; its presence does not mean every feature is
implemented. Mathematical arguments about geometric constructions, conditional
dispatch lemmas, numerical properties, and completed formal proofs have distinct
status. Consult the [README](../README.md) and individual development documents for
implemented syntax, build instructions, and validation results. The
[compiler protocol](protocol.md) defines communication between Rust and Lean.

The public implementation includes Stage 1b, path packages, finite abstract
selectors/contracts, edit assemblies, and protocol-6 reborrowing and authority
transfer. The declaration-driven indexed Core and the internal function, dispatch,
and authority checkers are connected through [public protocol 7](indexed-source.md).
The [finite geometry stdlib](../stdlib/src/geometry/README.md) now uses
`std::geometry::scheme` and `std::geometry::smooth`. The
[geometry migration acceptance map](geometry-migration.md) records finite
compatibility and semantic guarantees. The [Stage 1 completion ledger](stage1-completion.md)
tracks storage ownership, linear algebra, finite networks and performance evidence.
The Rust frontend is in `src/`, the mathlib-free Lean backend in `lean-kernel/`, and
the mathlib-dependent proof oracle in `lean/`; the oracle imports the actual backend
definitions. Ordinary compilation does not invoke the proof oracle.

Stage 0 geometry syntax remains supported for compatibility, so its specification
is not obsolete merely because it is old. General polynomial morphisms, AD,
numerical solvers, physical models, and evidence management are later work. This
index and draft do not establish implementation or proof of those features. See the
[mdBook migration plan](docs-cleanup-plan.md) for document classification and migration.

<a id="原文の保存確認"></a>

## Original-source preservation

Reconstructing the preface and all 18 sections from the split documents, and reversing
only the table-of-contents destination changes, reproduces the original UTF-8 bytes
exactly. [source-record.json](design/source-record.json) records the original filename,
whole-document and per-section SHA-256 hashes, destination files, and link rewrites.
The mathematical content has not been replaced with summaries. The English navigation
uses the existing English draft text; the preserved source blocks are unchanged.
