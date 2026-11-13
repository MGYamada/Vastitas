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
| Introduction and chapters 1–12 | Teaching chapters in reading order. Each ends with a **See also** section that links into the Vastitas Reference | `README.md`, `guide/*.md` |
| Vastitas Reference | The notation and the complete rules for each language construct | `language/`, `stage1a.md`, `stage1b.md`, `packages.md`, `indexed-source.md`, `affine-geometry.md`, `storage-ownership.md`, `storage/resource-programs.md`, `linalg/` |
| How the compiler is checked | Architecture, the driver, checking pipeline, wire protocols, proof boundaries and specifications | `development/architecture.md`, `internals/`, `storage/checked-storage.md`, `protocol.md`, `verification*`, `daleckii-krein.md`, `specifications.md`, `spec/` |
| Appendices A–H | CLI, diagnostics, reference models, limits, history and delivery records, contributing with the stdlib admission ADR, glossary, grammar summary | `appendix/`, `guide/cli.md`, `reference/`, `guide/historical-roadmap.md`, `stage1-*.md`, `stage2-acceptance.md`, `stage3-acceptance.md`, `reverse-core-acceptance.md`, `development/` apart from `architecture.md`, `adr/` |

File paths stay stable when a chapter moves between parts, because tests,
scripts, experiment records and external links name them.
`scripts/check_book.py` requires the Introduction as an unnumbered prefix
chapter followed by Getting Started. It reads the part of each chapter from the
part titles of `SUMMARY.md`, and chapters before the first part title form the
guide.

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

The generated site is in `target/book/`. `scripts/check_book.py` checks that:

- `SUMMARY.md` lists every chapter once, and mdBook rendered each of them;
- every local link and anchor of the rendered book resolves, and every link to
  a file of this repository on GitHub names a file at that revision, within
  its line count on `main`;
- every `docs/<chapter>.md#anchor` named in a file outside `docs/` names a
  chapter and one of its anchors, apart from recorded experiment runs and the
  unit tests of the checkers;
- every `docs/<chapter>.md` named in a file outside `docs/` without an anchor
  names a chapter;
- every redirect in `book.toml` leads from a retired chapter to a chapter and
  an anchor of the book;
- the Introduction links to the roadmap, and every formula of the rendered
  book carries its TeX source as an annotation;
- every `include` directive names a file and an anchor or line range in it;
- every complete program, a code block with `fn main`, comes from an
  `include` directive, and a chapter includes every file under `examples/book/`
  and `examples/reject/`;
- every Syntax block lies in the Vastitas Reference, holds productions only,
  and uses only tokens that the parser in `src/frontend*.rs` knows. The token
  check skips productions whose name is in UPPER_CASE, which define lexical
  forms;
- every nonterminal of a Syntax block has one production in the Reference, or
  a name in `PENDING_NONTERMINALS`. The Syntax block of
  [Notation](../language/notation.md) is an illustration and defines nothing;
- the [grammar summary](../appendix/grammar.md) is the text that
  `scripts/grammar_summary.py` generates from the Syntax blocks of the
  Reference;
- the productions of the grammar summary derive, from `SourceFile`, every
  source file under `examples/` and `stdlib/src/`, and they derive no file of
  a rejected program whose recorded diagnostic is `E_PARSE` or `E_LEX`.
  `scripts/book_grammar.py` tokenizes a file as
  [Lexical structure](../language/lexical-structure.md) says and recognizes it
  with the productions. A file of a rejected program with `E_UNSUPPORTED` or
  `E_RESERVED` is skipped, because these codes report text that the
  productions derive and text that they do not. `PARSE_EXCEPTIONS` names each
  file whose code a rule gives and the productions do not decide, with the
  rule, and the check fails on an entry that no longer holds;
- [Appendix D](../appendix/limits.md) has a table row with the value of
  each key of `lean-kernel/compiler-limits.json`, and no row with a key
  that the file lacks;
- the first line of a chapter is `#` and its title in `SUMMARY.md`, where an
  appendix title `G: Glossary` becomes `Appendix G: Glossary`;
- a chapter keeps the rules of the [style guide](#style-guide) that its part
  has, as [Checked rules](#checked-rules) lists.

The last two checks apply to every chapter of `SUMMARY.md` apart from the
archived delivery records, which `ARCHIVED` in `scripts/check_book.py` lists.
A chapter that joins `SUMMARY.md` is checked from its first change.
`PENDING_NONTERMINALS` names the nonterminals that a Syntax block uses before
the chapter that owns the construct defines them. Remove a name in the change
that adds its production; the check fails on a pending name that has one.
`python3 -m unittest discover -s scripts -p test_check_book.py` runs the
checker's own tests.

`scripts/check_grammar_derivations.py` checks the other direction with a
built compiler, and the CI job of the native compiler runs it. It derives
texts from the productions with a depth bound and a fixed seed: one text for
each nonterminal and each option of a choice or a repetition that no earlier
text covers, then free texts up to 500. It places each text in a small
program as an item, a statement, an expression, a type or a resource
statement, in flat mode and in manifest mode, and runs `vastitas check` on
it. A derived text gives no `E_PARSE`, `E_LEX` or `E_UNSUPPORTED`, unless a
rule of the Reference forbids it. `RULES` names each such rule with its
section and its codes. The first diagnostic of a text that breaks a rule has
one of those codes, or it is an error of another class at or before the
first place that breaks a rule, because the frontend checks some rules on
names and types while it parses and stops at the first error. Run it as
`python3 scripts/check_grammar_derivations.py --compiler
target/debug/vastitas` after a change of a Syntax block or of the parser;
`--seed` takes another fixed seed.

The grammar summary is a generated chapter. After a change of a Syntax block,
run `python3 scripts/grammar_summary.py --write` and commit the chapter with
the change. The chapter holds the productions in plain code blocks, not in
Syntax blocks, so the check of nonterminals counts no production of it as a
definition. Do not edit the chapter by hand.

The documentation workflow runs on
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
   `language/`, chapters on how the compiler works under `internals/`,
   appendix pages under `appendix/` and contributor procedures under
   `development/`. Reference chapters that predate `language/`, such as
   `stage1a.md` and `packages.md`, keep their paths. Link each retained
   chapter once from `docs/SUMMARY.md`. The Introduction links to the
   historical-stage guide and the main reader paths. A teaching chapter uses
   working programs from `examples/`, as [Examples](#examples) describes, and
   ends with a **See also** section that links the Reference sections whose
   rules it teaches.
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
   Add a redirect from a retired chapter to its replacement under
   `[output.html.redirect]` in `book.toml`.
5. Inspect the built chapter, search, equations, tables, attachments and
   navigation on desktop and narrow screens. Verify deployment base paths
   before publishing a site. The build artifact is available independently of
   a public hosting destination.

When a change moves or renames a section, repoint every link to it in the
same change: the links of the book, and the links in `README.md`, `stdlib/`,
`experiments/`, `scripts/` and `book.toml`. `scripts/check_book.py` fails on a
link of the book to an anchor that does not exist. A rewrite in several steps
may keep an old anchor for its duration, as `<a id="old-anchor"></a>` in a
list "Moved sections" at the end of the chapter, with a link to the section
that holds the content. Its last step removes these anchors. No chapter holds
one.

When a rewrite splits a chapter, the rules go to the Reference chapter and
the description of the compiler to a chapter under `internals/`. That chapter
ends with a section "History", a heading of level one or two with exactly
this title, which holds the issue links and the delivery record. The
chapters of the part "How the compiler is checked" that hold moved text keep
the wording of their source. The [checked rules](#checked-rules) of the part
apply to them, and the other rules of the style guide apply to the text that
a change adds or rewrites. A change of
source syntax that programs must follow goes under "Source migrations" in
[Appendix E](../appendix/history.md).

The first chapter was commissioned in
[#516](https://github.com/MGYamada/Vastitas/issues/516). Old v0.3 design
documents and superseded delivery plans were retired on 4 November 2026 JST.
Git retains the earlier revisions.

## Style guide

These rules govern the text of every chapter. The archived delivery records,
`stage1-completion.md` and the `stage*-acceptance.md` files, are exempt and keep
their original wording. So do the chapters with moved text that
[Author and retire a chapter](#author-and-retire-a-chapter) names, apart
from the checked rules.

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
  [glossary](../appendix/glossary.md). Set the term in bold where the text
  defines it, and nowhere else.
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
- State a limit as a number where a program meets it in ordinary use, such as
  the six parameters of a generic, and link
  [Appendix D](../appendix/limits.md), which lists every limit.
- Write "even when" for a case that a rule covers although a reader may expect
  an exception, and "including" for a case that belongs to a class.

### Examples

- Put every complete flat program in a file under
  `examples/book/<construct>/` and every package under `examples/packages/`,
  or use a program that `tests/examples.rs` already builds and runs. Pull it
  into the chapter with the mdBook
  [`include` directive](https://rust-lang.github.io/mdBook/format/mdbook.html#including-files),
  so that the book shows the tested text. Mark a part of a file with
  `// ANCHOR: name` and `// ANCHOR_END: name` comments to include only that
  part.
- List the program in `BOOK_PROGRAMS` or `BOOK_PACKAGES` in
  `tests/examples.rs` with the output that the chapter states.
  `cargo test --locked --test examples` builds and runs it, and fails on a
  file under `examples/book/` that the lists omit.
- Put a rejected program in `examples/reject/<construct>/` and list it in
  `BOOK_REJECTIONS`. The file `<name>.stderr` next to it holds the lines that
  `vastitas check` prints for it from the repository root. Include both files,
  so that the chapter shows the diagnostic that the compiler prints. Do not
  paraphrase the diagnostic.
- Put a rejected package in `examples/reject/packages/<name>/` and list the
  directory in `BOOK_REJECTED_PACKAGES`. `<name>.stderr` next to the directory
  holds the lines of `vastitas check --manifest-path`, with the repository root
  removed from file names. A chapter need not include the manifest.
- List a package whose build links OpenBLAS in `BOOK_NUMERICAL_PACKAGES`.
  Its test builds and runs the package only where the pinned OpenBLAS is
  available: `cargo test --locked --test examples -- --ignored` with
  `VASTITAS_TEST_OPENBLAS_PREFIX`. The numerical CI jobs run it.
- Put a package whose executable stops with a run-time diagnostic under
  `examples/packages/` and list its directory in `BOOK_RUNTIME_FAILURES`.
  `<name>.stderr` next to the directory holds the line that the executable
  writes to standard error.
- Label a manifest with `toml`.

### What stays out

- Issue and pull request links appear only in the appendices and in a
  History section at the end of a chapter in the part "How the compiler is
  checked". A generated specification chapter also links the issue of each
  Planned claim, because that issue is the claim's evidence.
- The guide's body contains no issue numbers, commit hashes, Stage numbers,
  wire-protocol numbers or theorem names.
- Evidence ledgers and proof-boundary lists belong in the part "How the
  compiler is checked" and in the appendices. Other chapters link to them.
  The Reference states a status in one place: the paragraph that begins "The
  evidence:" at the end of each section of
  [Guarantees](../language/guarantees.md). Such a paragraph is short. It
  gives the status words and links the chapter that holds the detail.
- The Vastitas Reference describes the language as it is. A section does not
  say which Stage or wire-protocol version introduced a construct.

### Principles and status words

- The Introduction must state the tagline *A Language for Math 2.0 and
  Physics 2.0* and the five design goals: Syntax like Rust, Experience like
  Julia, Philosophy like Haskell, Verification like Lean and Performance like
  C/C++. The design goals are aims, not claims about what exists.
- The Introduction states the performance goal **Fast like C** and the
  principle **Check before generating**, in at least one sentence each. **Fast
  like C** names the C/C++-class target of the Performance design goal; it is
  not a second performance requirement. Where a chapter states a performance
  target, it says C/C++-class.
- Use the status words Implemented, Tested, Proved and Planned with the
  meanings that the [Introduction](../index.md#what-exists-today) gives them,
  and keep the four apart. `AGENTS.md` requires this separation.
- A claim in a [specification](../specifications.md) has one of the six
  [claim statuses](../specifications.md#claim-statuses). The chapters under
  `docs/spec/` are generated: edit the TOML file, then run
  `python3 scripts/check_spec.py --write`.

### Checked rules

`scripts/check_book.py` enforces these rules on every chapter apart from the
archived delivery records. The other rules of this guide need a reviewer.

| Rule | Guide | Reference | Compiler checked | Appendices |
| --- | --- | --- | --- | --- |
| No "now", "currently", "new", "newly", "deliberately" or "actually" in prose | Yes | Yes | Yes | Yes |
| No intensifier "actual", "simply", "very" or "really" in prose | Yes | Yes | | |
| No "should" | | Yes | | |
| No Stage numbers | Yes | Yes | | |
| No wire-protocol version | Yes | Outside implementation notes | | |
| No issue or pull request references | Yes | Yes | Outside a History section | |
| No commit hashes or theorem names | Yes | | | |
| Ends with a See also section that links a Reference chapter | Yes, apart from the Introduction | | | |
| A term set in bold has a glossary entry | | Yes | | |
| A complete program, function or method comes from an `include` | Yes | Yes | Yes | Yes |
| The diagnostic of a rejected program comes from its `.stderr` file | Yes | Yes | Yes | Yes |
| An `include` selects a part of a file by `ANCHOR`, not by lines | Yes | Yes | Yes | Yes |

The word rules read prose only. They skip code, link targets, HTML, math and
words in double quotation marks, which mention a word rather than use it. The
delivery records are exempt from every rule. A generated specification chapter
may link issues outside a History section, as
[What stays out](#what-stays-out) says.

The glossary rule reads each paragraph as a whole, so a bold term may wrap,
and it reads `**term**` and `__term__`. It finds a term under its own name or
in the singular, among the titles of the glossary entries and the terms that
an entry sets in bold. Bold text that defines no term is exempt: the labels
**Syntax** and **Implementation note.**, and the rule words that
[Notation](../language/notation.md#rules) defines. `NOT_DEFINITIONS` in
`scripts/check_book.py` lists them. A complete function or method is a named
`fn`, `resource fn` or `method` whose signature a body follows, in a code block
labelled `vast` or without a label. A diagnostic is a line
`FILE:LINE:COLUMN: E_CODE: message` or `MANIFEST: E_CODE: message` in any code
block, where the place names a file and may hold spaces. A diagnostic without
a place is about a command, not a rejected program, and the forms of
[Diagnostic lines](../language/diagnostics.md#diagnostic-lines) name no file.
The See also rule reads inline links and reference links, and a link in code
or in an HTML comment links nothing.

## Consolidation baseline

The baseline before the migration contained 61 Markdown documents at
`cc4922f505077567c72848310fec2a7c7b812076`. Eleven original paths remain.
Thirteen superseded design or planning documents were retired, 36 source
documents were combined into topic chapters, and the rewrite of the Reference
retired one more chapter. This removes 50 of the 61 original paths (82.0%). Chapter content, code examples, theorem hypotheses and measured
profiles from the active documents were retained in the consolidated references.
The two compiler scaling CSV files remain attached to their reported revision.

| Former subjects | Current home |
| --- | --- |
| Abstract selectors and promotion policy | [Abstract types](../stage1a.md#abstract-types) · [Promotion](../stage1a.md#promotion) |
| Promotion proofs and old-checker indexing measurements | [Checking pipeline](../internals/checking-pipeline.md#promotion-proofs-and-fixture) · [History](../internals/checking-pipeline.md#history) |
| Edit grants, nested reborrowing and permanent transfer | [Edit authority](../language/edit-authority.md) |
| Declaration checker and geometry migration | [Indexed declarations](../indexed-source.md) · [The indexed checker](../internals/indexed-checker.md) · [History](../internals/indexed-checker.md#history) |
| Layout preflight, raw ownership IR, resource calls | [Checked storage](../storage/checked-storage.md) |
| Public resource statements and runtime shapes | [Resource programs](../storage/resource-programs.md) |
| Numerical declarations, owned maps and optional BLAS | [Numerical maps](../linalg/maps-and-gemm.md) · [Numerical backend](../internals/numerical-backend.md) |
| Transforms, vectors and explicit metrics | [Transforms, evaluation and metrics](../linalg/transforms-and-metrics.md) · [Numerical backend](../internals/numerical-backend.md#transforms-vectors-and-metrics) |
| Network wiring, contraction trees and cached packing | [Networks, packing and contraction trees](../linalg/networks-and-packing.md) · [Numerical backend](../internals/numerical-backend.md#networks-packing-and-contraction-trees) |
| Pure evaluator and categorical crossing-word checker | [Core and graph proofs](../verification/core-models.md) |
| Standalone development and mathematical references | [Compiler tools](../reference/compiler-tools.md) · [Analysis and effects](../reference/analysis-and-effects.md) · [Geometry](../reference/geometry.md) |
