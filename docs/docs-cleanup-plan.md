<a id="stage-1-完了後の-docs-cleanup-と-mdbook-導入計画"></a>

# Documentation cleanup and mdBook adoption after Stage 1

Status: plan, with English-language preparation completed before Stage 1 at the
user's request. Book reorganization, mdBook installation, and site publication remain
after the Stage 1 completion record; none is claimed complete here.

Created: 27 October 2026 (JST). Updated: 29 October 2026 (JST). The inventory now uses
PR #234's merge `4de22b4` and the documentation in this revision as its baseline.
The [README](../README.md), [Stage 1 completion ledger](stage1-completion.md), tests,
and validation records remain the implementation sources of truth. Repeat the
inventory when migration starts and pin the completed implementation commit.
This document plans documentation work; it does not expand the implemented Stage 1
scope or formal-verification claims.

<a id="1-開始条件と整理の目的"></a>

## 1. Entry conditions and purpose

The public implementation includes Stage 1b, path packages / call-only module
imports, finite abstract selectors/contracts, edit assemblies, protocol-6
reborrowing and authority transfer, and protocol-7 indexed declarations with the
finite geometry stdlib. This is not completion of the entire historical Stage 1.
[Stage 1 in v0.3](design/roadmap-acceptance.md#14-initial-implementation-sequence)
includes independent lambdas and finite dispatch, function edit authority,
composition of declarative differences, footprints, obligation transfer and repair,
storage ownership, basic linear algebra, and more.

Before starting the book reorganization, record the following in the implementation roadmap:

- The Stage 1 scope and acceptance criteria, with corresponding implementation,
  test, proof, and CI evidence.
- The completed commit or tag, remaining limitations, and open questions.
- Any scope changes from the original design, their reasons, and the new destination
  of deferred items. Do not silently mark unimplemented items complete.

Once that baseline is established, organize the documents so readers can distinguish
available features, usage, guarantees, and future design. Continue correctness fixes
alongside ordinary development until Stage 1 is complete. Cleanup must not change
language semantics or the meaning of proofs; investigate the evidence before fixing
inconsistencies.

**Fast like C is the highest-priority performance and architecture goal.** Include the
[revised Chapter 7](storage-ownership.md) contracts for layout, aliasing, residual
retention, costs, and C-comparison acceptance without implying implementation.
The book structure must give ownership and storage the same depth of treatment as
dispatch. Current preparation covers inventory, planning, necessary design revisions,
and English documentation. Install/configure mdBook, reorganize book content, and
publish the site only after recording Stage 1 completion.

### English preparation before Stage 1 completion

Use English for the documentation's reader-facing prose. The implementation
specifications and preserved v0.3 draft are already English. Translate the design
index, this migration plan, and the navigation of the eight draft documents.
Preserve equations, code, qualifications, section numbers, and source-record hashes.
Keep existing Japanese heading anchors as invisible compatibility targets when
translating headings; do not maintain duplicate language editions or translate
historical source blocks that are already English.

Check local links and both old and new anchors, scan for untranslated prose, and
reconstruct the original draft against `source-record.json`. This preparation does
not require mdBook installation and does not change Stage 1 acceptance criteria.

English preparation validation (29 October 2026): all 33 Markdown documents under
`docs/` have English reader-facing prose; the ten changed documents retain all
14 original heading anchors and pass 65 local link/fragment checks. Reconstructing
the preface and all 18 draft sections yields the original 145,829 bytes and SHA-256
`4bc09c0c4a168dcbacc3e982750fb922a1b1ca0302746445088b1ae2ef4da456`.
The preservation record is unchanged. Japanese remains only in invisible legacy
anchor identifiers. Rendering with mdBook is deferred to adoption.

<a id="2-文書の役割と正本"></a>

## 2. Document roles and sources of truth

| Documents | Role after cleanup | Policy |
| --- | --- | --- |
| Root `README.md` | Repository entrypoint | Keep the overview, current milestone, shortest build example, and links to the book and detailed specifications |
| `docs/README.md` (new) | Book entrypoint | Add reader-oriented navigation and an implementation-status table; do not duplicate all README instructions |
| `docs/guide/` (new) | Usage guide | Cover setup, CLI, examples, library use, and diagnostics |
| `docs/stage0.md`, `stage1a.md`, `stage1b.md`, `packages.md` | Implementation specifications | Retain existing paths; reconcile contracts/limits at Stage 1 completion and link subsequent increments |
| `docs/protocol.md` | Frontend/kernel contract | Distinguish public wire protocols from internal Core, and document compatibility/independent-checking boundaries |
| `docs/verification.md` | Source of truth for proof scope | Distinguish theorems, actual implementation definitions, assumptions, unproved parts, and regressions |
| `docs/development/` (new) | Contributor procedures | Collect architecture, validation commands, and documentation maintenance |
| `docs/stage1-completion.md`, `stage1-roadmap.md`, `stage1-delivery.md`, this plan | Completion ledger, development plans, and history | Separate the current ledger from historical snapshots; direct readers to individual specifications for current contracts |
| `docs/design.md`, `docs/design/` | Historical design and research context | Preserve v0.3 source blocks; describe differences from current specifications outside those blocks |
| `docs/storage-ownership.md`, `docs/adr/` | Adopted designs and policy | Display adopted contracts separately from implementation, proof, and performance-measurement status |
| `stdlib/README.md`, `AGENTS.md` | Directory entrypoint / contributor guidance | Link standard-library details to the book's source of truth while retaining an entrypoint; reference contributor guidance rather than copying it |

The implementation-status table should have columns for feature, specification,
implementation/regressions, proofs/assumptions, and limitations/follow-up work.
Implemented, tested, proved, assumed, proposed, and deferred are distinct states.
Keep the README's short status summary synchronized with this table and link proof
descriptions to `verification.md`. English preparation is authorized before the
book migration; maintaining synchronized bilingual editions is outside this plan.

Pay particular attention to:

- Updating any Stage-0-centered implementation guidance in `docs/design.md`
  outside the preserved source blocks.
- Keeping import guidance in `stdlib/README.md` consistent with explicit `--lib`
  versus package mode.
- Reconciling “future” / “unimplemented” wording and roadmap tense with the
  implementation at the completion baseline.
- Cross-checking all public protocols at completion, `--lib` / `--manifest-path`,
  defining modules, and call authority. Do not confuse current protocols 2–7 with
  planned protocol 8.
- Preserving Rust acceptance versus Lean semantic acceptance, and the dependency
  boundary between the ordinary compiler and proof oracle.

<a id="21-現在の全資料の配置先"></a>

### 2.1 Inventory and destinations

Do not classify a document as obsolete based on its filename's age. Supported
compatibility specifications, historical validation evidence, and adopted but
unimplemented designs require different treatment. The following inventory covers
all current Markdown documents and attached data under `docs/`.

| Current path (relative to `docs/`) | Classification / book placement | Migration treatment |
| --- | --- | --- |
| `stage0.md` | Current compatibility-language specification | State the supported legacy geometry and `--lib` scope; do not mark the entire document obsolete |
| `stage1a.md`, `stage1b.md` | Current language specifications | Keep as the dispatch and independent-function sources of truth; update cross-references |
| `packages.md`, `abstract-types.md`, `promotion.md` | Current language/stdlib specifications | Preserve packages, abstract selectors, and value-promotion policy |
| `edit-borrowing.md`, `edit-authority.md` | Current edit-authority specifications | Distinguish protocols 5/6, definition identity versus edit authority, loans, and transfer |
| `indexed-declarations.md`, `indexed-source.md` | Public indexed syntax, internal implementation, and migration status | Distinguish public protocol 7, internal checkers, compatibility adapters, the migrated finite geometry stdlib, and remaining migration/proof work |
| `storage-ownership.md` | Adopted design / revised Chapter 7 | Source of truth for layout, aliasing, residual retention, costs, and performance acceptance; link implementation evidence to the ledger |
| `storage-layout-preflight.md` | Executable storage-layout reference / pending compiler integration | Keep reference validation distinct from production ownership, native GEMM, and measured C performance |
| `symplectic-reference.md`, `l2-tail-reference.md` | Executable mathematical references / later features | Preserve exact contracts and limitations; do not present Python references as public compiler features |
| `identifier-ascii-reference.md`, `identifier-ascii-validation.md` | Identifier round-trip reference / pending frontend integration | Preserve the fixed Unicode profile, exact-name policy, metadata and authority boundary; keep reference tests distinct from compiler acceptance and meaning preservation |
| `protocol.md`, `verification.md` | Public boundary / verification sources of truth | Reconcile versions, actual checkers, theorems, assumptions, and unproved obligations |
| `adr/0001-mathematics-first-stdlib.md` | Adopted policy / ADR | Check the merged policy status; distinguish later ADRs and implementation status |
| `graph-crossings.md` | Internal implementation / later feature | State the finite crossing checker's scope; do not equate it with completed Stage 1 networks |
| `graph-proof-obligations.md` | Open design / proof obligations | Place under future research/planning, not completed proofs |
| `stage1-completion.md` | Current completion ledger | Entry point for completion commits, acceptance criteria, performance measurements, and limitations |
| `stage1-roadmap.md` | Historical sequence / milestone records | Place under history; label old “next” statements as historical and link the current ledger |
| `stage1-delivery.md` | Protocol-5-era history | Retain as an issue snapshot from that time, not the current open-issue list |
| `stage1b-indexing.md` | Implementation/performance investigation evidence | Preserve measured commits and conditions; distinguish compilation measurements from current executable performance |
| `benchmarks/stage1b-{original,main}-comparison.csv` | Two measurement data attachments | Distribute unchanged and link from the investigation document |
| `docs-cleanup-plan.md` | Migration / maintenance plan | Record each stage's implementation commit and unfinished work |
| `design.md` | Current design index | Entry point to adopted designs and preserved drafts; correct stale guidance outside original-source blocks |
| `design/vision-status.md`, `geometry.md`, `tensor-resources-units.md`, `functions-dispatch.md` | Preserved v0.3 draft (preface, Sections 1–8) | Keep original-source blocks immutable; add current-specification guidance outside them |
| `design/differentiation-spectral.md`, `physics-compiler-verification.md`, `roadmap-acceptance.md`, `history-references.md` | Preserved v0.3 draft (Sections 9–18) | Same policy; distinguish adopted design, future proposals, and obsolete portions by section |
| `design/source-record.json` | Original-source preservation evidence | Retain destinations, reverse rewrites, byte counts, and hashes for reconstruction checks |

Track the root README, `stdlib/README.md`, `AGENTS.md`, examples, and validation
scripts separately as sources outside the book. Add rows for specifications, ADRs,
and attachments introduced before the migration baseline is fixed.

<a id="22-obsolete文書と検索の扱い"></a>

### 2.2 Obsolete documents and search

Give every page a status—current specification, adopted design awaiting
implementation, internal implementation, history, or preserved draft—together with
a baseline commit/date and a link to its successor source of truth. Mark content
obsolete only when it is fully superseded, and explain why with a successor link.
Do not replace old test evidence with current results or delete future proposals
merely by labeling them obsolete.

For example, direct readers from original Chapter 7 to the revised chapter, and
from the implemented portions of original Section 8.3 to `stage1a.md`,
`edit-borrowing.md`, and `edit-authority.md`. Do not treat the full draft as current
specification. Put current documents first in normal navigation, with history and
preserved drafts in a separate appendix. Make status visible in search-result
titles or guidance. Verify whether the pinned mdBook version supports excluding
individual chapters from search; otherwise distinguish them with visible labels.
Do not assume an unverified configuration option exists.

Preserve old Markdown paths and heading anchors by default. If a move is necessary,
record old path/anchor, successor path/anchor, and referring documents, and leave
navigation at the old page. HTML redirects alone do not repair GitHub Markdown
links, so test both. Do not silently redirect an old anchor to a chapter with a
different meaning.

<a id="3-mdbook-の構成"></a>

## 3. mdBook structure

Add `book.toml` at the repository root and `SUMMARY.md` under `docs/`, using the
existing Markdown directly as book input. Organize readers' paths through the table
of contents rather than maintaining duplicate book text. Avoid bulk moves or
renames of existing specifications; include a mapping, old-link handling, and
referring-link updates in any necessary move.

The planned contents follow. Add new pages to the contents only after writing them.

```text
Entry and implementation status   docs/README.md
Usage guide                       docs/guide/{getting-started,cli,stdlib}.md
Language specification            docs/{stage0,stage1a,stage1b,packages}.md
                                  + specifications added before Stage 1 completion
Storage and performance           docs/storage-ownership.md and measurement records
Implementation and verification   docs/development/{architecture,validation}.md
                                  docs/{protocol,verification}.md
Design policy and open designs    docs/adr/ and later-feature design documents
Current completion ledger         docs/stage1-completion.md
History and preserved drafts      docs/design.md and all eight docs/design/ documents
                                  docs/{stage1-roadmap,stage1-delivery,stage1b-indexing}.md
Migration and maintenance         docs/docs-cleanup-plan.md
                                  docs/development/documentation.md
```

The initial configuration below is an example to validate during adoption, not a
current build procedure. Follow the
[configuration specification](https://rust-lang.github.io/mdBook/format/configuration/general.html)
and [contents format](https://rust-lang.github.io/mdBook/format/summary.html).

```toml
[book]
title = "Vastitas Programming Language"
authors = ["Vastitas Project Contributors"]
language = "en"
src = "docs"

[build]
build-dir = "target/book"
create-missing = false

[output.html]
mathjax-support = true

[output.html.playground]
runnable = false
```

Use `Vastitas Programming Language` as the book title and
`Vastitas Project Contributors` as the author name. Show
`Copyright 2026 Vastitas Project Contributors` and an Apache License, Version 2.0
notice at the book entrypoint, consistent with the repository README and LICENSE.

Place generated output under the already ignored `target/` directory and do not
commit it. `create-missing = false` prevents typo-driven empty chapter creation.
Pin mdBook as a documentation development tool; do not add it to compiler Cargo or
Lake dependencies. Select a compatible version at adoption and use the same pin
locally and in CI. The default installation command is
`cargo install mdbook --version '=SELECTED_VERSION' --locked`. Consult the
[official CI guide](https://rust-lang.github.io/mdBook/continuous-integration.html)
and pin Actions to commit SHAs, as in the existing CI.

<a id="数式コードリンクの互換性"></a>

### Mathematics, code, and link compatibility

- v0.3 contains `$...$` / `$$...$$`; do not assume `mathjax-support = true` alone
  renders them correctly. The [official MathJax documentation](https://rust-lang.github.io/mdBook/format/mathjax.html)
  describes delimiter restrictions. Test equations, multiline expressions, and
  mathematics in tables with the adopted version. If needed, add minimal
  render-time conversion; do not directly rewrite preserved equations or escapes.
- Preserve `draft-v0.3:*` blocks, section numbers, assumptions, qualifications,
  references, and [source-record.json](design/source-record.json). Reverse the
  original contents-link rewrites and check byte counts and SHA-256 hashes of
  every section and the reconstructed whole. Never update recorded hashes to
  conceal a mismatch.
- Label runnable examples `vast`, shell commands `sh`, and design pseudocode
  explicitly as such. Vastitas highlighting can follow later; do not expose a
  UI that runs these examples as Rust.
- Arrange links outside `docs/`, including README, AGENTS, examples, and source,
  so generated HTML does not point to nonexistent relative paths. Link to book
  explanations or the corresponding repository files. Handle any necessary
  preserved-text adjustments at rendering time.
- Verify cross-references, heading anchors, images, and attachments such as
  `source-record.json` in both GitHub Markdown and generated HTML.

<a id="4-実施順序と成果物"></a>

## 4. Sequence and deliverables

| Stage | Work | Completion criterion |
| --- | --- | --- |
| 0. English preparation | Translate remaining navigation/planning prose before Stage 1; preserve original draft blocks and old anchors | English prose, valid links/anchors, and matching source hashes; no mdBook dependency added |
| 1. Inventory | Fix the Stage 1 completion baseline and reconcile this inventory with every page, duplicate, stale statement, and reference | Every file has a classification, source of truth, status, destination, preservation policy, and basis for corrections |
| 2. Content organization | Prepare implementation status, usage guidance, and contributor procedures; synchronize specifications, proof scope, and README | Readers can distinguish current specifications from historical proposals and trace examples/evidence |
| 3. mdBook adoption | Add the pinned version, `book.toml`, `SUMMARY.md`, and minimal rendering support | Local build/serve works; equations, code, and every chapter are visually checked |
| 4. CI and maintenance | Add docs build, link/source-preservation checks, procedures, and an HTML artifact | PR output is reviewable; broken chapters, links, and changes to preserved text are detected |
| 5. Publication | After local/CI completion, choose the destination, branch, and URL and configure deployment | Record the published URL and update procedure; verify the real site's navigation, including subpaths |

Keep English preparation, stages 1–2 content work, stage 3 book configuration,
stage 4 checks/maintenance, and stage 5 publication in separate reviewable changes.
Record affected documents and rendering/link checks in each PR. Keep existing
Markdown readable if adoption encounters problems; do not make generated HTML the
only place information exists. Do not mix mdBook dependencies into Stage 1
implementation PRs.

Treat mdBook adoption and site publication as separate deliverables so stages 1–4
can finish before a publication destination is chosen. GitHub Pages is the first
candidate. If adopted, configure `site-url` for the project URL; PRs validate and
produce artifacts, while publication is restricted to successful validation of the
selected branch or tag. Limit deployment permissions to the deployment job. This
plan and English preparation do not change deployment configuration.

<a id="5-検証と保守"></a>

## 5. Validation and maintenance

Keep documentation CI separate from compiler/oracle jobs. The book should build
from Markdown, configuration, and rendering resources alone. Preserve ordinary
compiler no-mathlib CI.

| Area | Validation at adoption |
| --- | --- |
| Structure and generation | Pinned `mdbook build`, existence of every listed file, unintended empty chapters, and omitted pages |
| Links | Check local Markdown references and generated HTML files/anchors; keep network-dependent external-link checks separate |
| Source preservation | Reconstruct all sections and the whole document using `source-record.json`; ensure rendering does not modify inputs |
| Presentation | Use `mdbook serve` to inspect contents, search, English prose and Unicode, equations, tables, code, narrow screens, and published-subpath navigation |
| Executable examples | Build the kernel first; run `vastitas check` / `vastitas build` and compare generated-program output |
| Rejection and compatibility | Use relevant existing tests for diagnostic categories, all public protocols at completion, and `--lib` / package mode; add meaningful regressions for new examples |
| Status and performance | Check obsolete-page successors, revised Chapter 7 implementation status, C-comparison conditions/data, and unmet goals; do not confuse compilation time with executable runtime |
| Proof descriptions | Reconcile implementation definitions, theorem names, assumptions, and CI evidence; changes to proofs/kernel require the full prescribed validation for that subsystem |

[`mdbook test`](https://rust-lang.github.io/mdBook/cli/test.html) targets Rust code
examples and does not replace `.vast` validation. Keep runnable examples in
`examples/` or existing regressions where possible and record their relationship
to documentation snippets. Do not count historical pseudocode as a current
compiler success case.

`docs/development/documentation.md` should cover installing the pinned version,
`mdbook build` / `mdbook serve`, chapter additions, link checks, example updates,
original-source preservation, and publication. PRs changing CLI, language,
protocols, or proof scope must also update the corresponding source of truth and
implementation-status table.

<a id="6-完了チェックリスト"></a>

## 6. Completion checklist

- [x] English preparation is recorded with prose, link/anchor, and source-hash checks.
- [ ] Stage 1 completion criteria, commit, evidence, and remaining limits are recorded.
- [ ] Readers can navigate usage, current specifications, implementation/proof boundaries, and historical design separately.
- [ ] Every resource has a classification and source of truth; obsolete pages identify successors/reasons, without incorrectly retiring compatibility specifications or historical evidence.
- [ ] Revised Chapter 7 cost/performance contracts are included, with measured Fast like C scope and unmet goals traceable from implementation status.
- [ ] Duplicated explanations have a designated source of truth, reachable from README and existing entrypoints.
- [ ] The v0.3 preface and all 18 sections are preserved with matching hashes.
- [ ] Pinned mdBook builds locally and in CI; internal links and attachments open.
- [ ] Old Markdown paths/headings and HTML references are checked; moves have mappings and compatibility navigation.
- [ ] Equations, tables, code, contents, and search are visually checked, with problems and search limitations recorded.
- [ ] Example check/build/output and rejection behavior are verified, with actual commands/results recorded.
- [ ] Ordinary compilation and generated executables have no added mdBook or mathlib dependency.
- [ ] Documentation-update procedures and CI-artifact inspection are documented.
- [ ] If published, the URL, deployment conditions, and real-site verification are recorded.
