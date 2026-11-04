# Maintain the documentation

The book uses the Markdown files under `docs/` directly. The
[roadmap](../guide/historical-roadmap.md) records proposed work under the
current GitHub issue decisions. The [delivery ledger](../stage1-completion.md)
records accepted revisions. Use the [verification reference](../verification.md)
for theorem statements, assumptions and native boundaries.

## Book structure

The guide follows the shape of *The Rust Programming Language*, and the
Vastitas Reference follows *The Rust Reference*. `SUMMARY.md` defines four
parts:

| Part | Content | Files |
| --- | --- | --- |
| Introduction and chapters 1–12 | Teaching chapters in reading order, with short **What is checked** notes that link to the reference parts | `README.md`, `guide/*.md`, `affine-geometry.md` |
| Vastitas Reference | The notation and the complete rules for each language construct | `language/`, `stage0.md`, `stage1a.md`, `stage1b.md`, `packages.md`, `indexed-source.md`, `storage*`, `linalg/` |
| How the compiler is checked | Architecture, wire protocols, proof boundaries and the stdlib admission ADR | `development/architecture.md`, `protocol.md`, `verification*`, `daleckii-krein.md`, `adr/` |
| Appendices A–G | CLI, diagnostics, reference models, limits, history and delivery records, contributing, glossary | `appendix/`, `guide/cli.md`, `reference/`, `guide/historical-roadmap.md`, `stage1-*.md`, `stage2-acceptance.md`, `stage3-acceptance.md`, `development/` |

File paths stay stable when a chapter moves between parts, because tests,
scripts, experiment records and external links name them.
`scripts/check_book.py` requires the Introduction as an unnumbered prefix
chapter followed by Getting Started.

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

1. Put teaching chapters under `guide/`, Vastitas Reference chapters under
   `language/`, appendix pages under `appendix/` and contributor procedures
   under `development/`. Reference chapters that predate `language/`, such as
   `stage1a.md` and `packages.md`, keep their paths. Link each retained
   chapter once from `docs/SUMMARY.md`. The Introduction links to the
   historical-stage guide and the main reader paths. A teaching chapter uses
   working programs from `examples/`, as [Examples](#examples) describes, and
   ends with a **What is checked** note.
   Write every chapter by the [style guide](#style-guide).
2. Link other book chapters and bundled assets with relative paths. Link the
   Introduction as `index.md`, because mdBook renders `README.md` as
   `index.html`. Link repository source, examples and external experiment
   records to their GitHub locations. Use specific revisions when attributing measurements
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

## Style guide

These rules govern the text of every chapter. The archived delivery records,
`stage1-completion.md` and the `stage*-acceptance.md` files, are exempt and keep
their original wording. A chapter written before this guide adopts it in its
next rewrite.

### Voice

- Use the present tense and the active voice. Write "the kernel rejects the
  call", not "the call will be rejected".
- Put one idea in each sentence. Split a sentence longer than about 30 words.
- Do not write "now", "new" or "currently". The book describes the language as
  it is, and Git records how it changed. Write "fresh" for an identity that a
  construction creates.
- Do not use intensifiers such as "actual", "exact", "strict" or
  "deliberately". Use such a word only when it carries a technical meaning, as
  in "an exact field".

### Terms

- Define a term before you use it, and add it to the
  [glossary](../appendix/glossary.md).
- Use one word for one concept. Where a word has two meanings and the context
  does not decide, qualify it, as in edit loan and storage loan.

### Rules and their placement

- Write normative text with the rule words "must", "must not", "may" and "is
  an error (`E_CODE`)". [Notation](../language/notation.md#rules) defines what
  they mean. Normative text never uses "should".
- Every rule lives in one place, normally a section of the Vastitas Reference.
  Other chapters link to that section instead of restating the rule. The guide
  may describe a rule informally next to such a link.
- Lay out each Reference section on a construct as
  [Notation](../language/notation.md#sections) describes.
- Put implementation detail in an
  [implementation note](../language/notation.md#implementation-notes), so that
  readers can skip it.

### Examples

- Put every complete program in a file under `examples/book/`, or use a
  tested package under `examples/packages/`. Pull it into
  the chapter with the mdBook
  [`include` directive](https://rust-lang.github.io/mdBook/format/mdbook.html#including-files),
  so that the book shows the tested text. Step 3 of
  [Author and retire a chapter](#author-and-retire-a-chapter) requires a test
  for it.
- Show a rejected program with the diagnostic line that the compiler prints
  for it. Do not paraphrase the diagnostic.

### What stays out

- Issue and pull request links appear only in the appendices and in a
  History section at the end of a chapter in the part "How the compiler is
  checked".
- The guide's body contains no issue numbers, commit hashes, Stage numbers,
  wire-protocol numbers or theorem names.
- Evidence ledgers and proof-boundary lists belong in the part "How the
  compiler is checked" and in the appendices. Other chapters link to them.
- The Vastitas Reference describes the language as it is. A section does not
  say which Stage or wire-protocol version introduced a construct.

### Principles and status words

- The Introduction states the performance goal **Fast like C** and the
  principle **Check before generating**, in at least one sentence each.
- Use the status words Implemented, Tested, Proved and Planned with the
  meanings that the [Introduction](../index.md#what-exists-today) gives them,
  and keep the four apart. `AGENTS.md` requires this separation.

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
