# Maintain the documentation

The book uses the Markdown files under `docs/` directly. The
[roadmap](../guide/historical-roadmap.md) records proposed work under the
current GitHub issue decisions. The [delivery ledger](../stage1-completion.md)
records accepted revisions. Use the [verification reference](../verification.md)
for theorem statements, assumptions and native boundaries.

## Book structure

The book follows the shape of *The Rust Programming Language*. `SUMMARY.md`
defines four parts:

| Part | Content | Files |
| --- | --- | --- |
| Introduction and chapters 1–11 | Teaching chapters in reading order, with short **What is checked** notes that link to the reference parts | `README.md`, `guide/*.md`, `affine-geometry.md` |
| Language reference | The complete contract for each language feature | `stage0.md`, `stage1a.md`, `stage1b.md`, `packages.md`, `indexed-source.md`, `storage*`, `linalg/` |
| How the compiler is checked | Architecture, wire protocols, proof boundaries and the stdlib admission ADR | `development/architecture.md`, `protocol.md`, `verification*`, `daleckii-krein.md`, `adr/` |
| Appendices A–F | CLI, diagnostics, reference models, limits, history and delivery records, contributing | `appendix/`, `guide/cli.md`, `reference/`, `guide/historical-roadmap.md`, `stage1-*.md`, `development/` |

File paths stay stable when a chapter moves between parts, because tests,
scripts, experiment records and external links name them. The teaching chapters
keep evidence ledgers, revision hashes and proof-boundary lists out of their
text and link to the reference parts instead. `scripts/check_book.py` requires
the Introduction as an unnumbered prefix chapter followed by Getting Started.

Chapter 8 is reserved for `affine-geometry.md`, the historical Stage 2 chapter.
Until that file exists on `main`, `SUMMARY.md` lists it as an mdBook draft
chapter with an empty link. Replace `()` with `(affine-geometry.md)` when the
file lands.

## Build, check and preview

Run from the repository root with the documentation version pinned in
`config/mdbook-version`.

```sh
cargo install mdbook --locked --version "=$(cat config/mdbook-version)"
cargo install mdbook-katex --locked --version "=$(cat config/mdbook-katex-version)"
mdbook build
python3 scripts/check_book.py
python3 scripts/check_docs.py
mdbook serve --open
```

The generated site is in `target/book/`. The documentation workflow runs on
push and pull request, checks the downloaded Linux release against its SHA-256,
and retains the rendered HTML as an artifact for seven days. The compiler and
Lean builds have independent dependency lists.
[Documentation workflow](https://github.com/MGYamada/Vastitas/blob/main/.github/workflows/documentation.yml)

Keep mathematical expressions in their Markdown TeX form. The pinned
documentation preprocessor generates MathML during the build, so readers
can view the formulas offline. Invalid TeX stops the documentation build.
The renderer reports its build against the mdBook 0.5.3 preprocessor API.
The book is built with mdBook 0.5.4 and its MathML is checked in the generated HTML.

## Author and retire a chapter

1. Put teaching chapters under `guide/`, appendix landing pages under
   `appendix/` and contributor procedures under `development/`. Link each
   retained chapter once from `docs/SUMMARY.md`. The Introduction links to the
   historical-stage guide and the main reader paths. A new teaching chapter
   uses working programs from `examples/` and ends with a **What is checked**
   note.
2. Link other book chapters and bundled assets with relative paths. Link
   repository source, examples and external experiment records to their
   GitHub locations. Use specific revisions when attributing measurements
   or proof results. Verify both Markdown and rendered anchors after a move.
3. Label examples with their language. Use `sh` for shell commands, `vast` for
   Vastitas source and `text` for grammar, output and pseudocode. Run changed
   examples through the public CLI and test their stated outputs or diagnostics.
4. Distinguish shipped features, internal checkers, mathematical references,
   conditional proofs, measured results and proposals. When a design has been
   superseded, remove the old page and update callers, tests and navigation.
   Retain original measurement data and its scope with the corresponding record.
5. Inspect the built chapter, search, equations, tables, attachments and
   navigation on desktop and narrow screens. Verify deployment base paths
   before publishing a site. The build artifact is available independently of
   a public hosting destination.

The first chapter was commissioned in
[#516](https://github.com/MGYamada/Vastitas/issues/516). Old v0.3 design
documents and superseded delivery plans were retired on 4 November 2026 JST.
Git retains the earlier revisions.

## Consolidation baseline

The baseline before the migration contained 61 Markdown documents at
`cc4922f505077567c72848310fec2a7c7b812076`. Twelve original paths remain.
Thirteen superseded design or planning documents were retired and 36 source
documents were combined into topic chapters. This removes 49 of the 61 original
paths (80.3%). Chapter content, code examples, theorem hypotheses and measured
profiles from the active documents were retained in the consolidated references.
The two compiler scaling CSV files remain attached to their reported revision.

| Former subjects | Current home |
| --- | --- |
| Abstract selectors, promotion policy and proofs | [Finite dispatch](../stage1a.md#abstract-types) |
| Old-checker indexing measurements | [Functions and indexing evidence](../stage1b.md#stage1b-indexing) |
| Edit grants, nested reborrowing and permanent transfer | [Package authority](../packages.md#edit-borrowing) |
| Declaration checker and geometry migration | [Indexed language and geometry](../indexed-source.md#indexed-declarations) |
| Layout preflight, raw ownership IR, resource calls | [Checked storage](../storage/checked-storage.md) |
| Public resource statements and runtime shapes | [Resource programs](../storage/resource-programs.md) |
| Numerical declarations, owned maps and optional BLAS | [Maps and GEMM](../linalg/maps-and-gemm.md) |
| Transforms, vectors and explicit metrics | [Transforms and metrics](../linalg/transforms-and-metrics.md) |
| Network wiring, contraction trees and cached packing | [Networks and packing](../linalg/networks-and-packing.md) |
| Pure evaluator and categorical crossing-word checker | [Core and graph proofs](../verification/core-models.md) |
| Standalone development and mathematical references | [Compiler tools](../reference/compiler-tools.md) · [Analysis and effects](../reference/analysis-and-effects.md) · [Geometry](../reference/geometry.md) |
