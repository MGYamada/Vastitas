# Introduction

Vastitas compiles mathematical programs written in `.vast` to native
executables. A Rust frontend reads the source. An independent Lean kernel then
checks the whole program before any code is generated.

The finite Stage 1 compiler includes functions and dispatch, ordinary and smooth
affine geometry, storage ownership, real and complex matrix multiplication, and
checked tensor contraction trees.
[Stage 1 delivery and evidence](stage1-completion.md)

## Who this book is for

This book is for two kinds of reader:

- people who want to write and run `.vast` programs with the current compiler;
- contributors who need to know exactly what the compiler checks and what it
  does not.

The first chapters assume only some experience with a typed programming
language. The geometry and numerical chapters use some linear algebra and
algebraic geometry, and each chapter explains what it needs.

## Design goals

**Fast like C** is the primary performance goal. A mathematical abstraction must
compile to code with the storage access, allocation and kernel calls of a
competent C implementation of the same computation. Explicit layout and alias
checks, destination and scratch reuse, and visible allocation, packing and
retention costs govern the numerical design. The goal is not a claim about
current performance. Stage 2 or later owns the controlled Linux comparison with
standalone C and the outstanding tiny-call and total-cost acceptance.
[Storage and performance contract](storage-ownership.md)

Four further principles run through the book:

- **Check before generating.** The frontend's names and annotations are not
  trusted. The Lean kernel resolves names, allocates identities and checks every
  body, including bodies that are never called, before code generation.
- **Mathematical identity is nominal.** Two spaces with equal dimensions are
  still different spaces. A point remembers the object it lies on.
- **Nothing implicit.** There are no implicit numeric conversions. Numerical
  and storage operations never insert a conjugation, metric, copy or
  allocation for you.
- **Bounded and finite.** The checker publishes limits on nesting,
  specialization, dispatch keys and checking work. An input that exceeds one is
  rejected, usually with `E_LIMIT`, and never partially accepted. Some costs, such as total
  compiler wall time, are not bounded yet.

## What exists today

The current compiler implements the finite Stage 1 profile, with the standard
library in `stdlib/` and the programs in `examples/`. Historical Stage 2 (finite affine geometry over
QQ, [tracker #571](https://github.com/MGYamada/Vastitas/issues/571)) adds
[presented affine geometry](affine-geometry.md), also available as
`std::geometry::scheme::affine`. Its [acceptance map](stage2-acceptance.md)
separates what is proved, tested and still pending.
Historical Stage 3 (finite smooth affine geometry over QQ,
[tracker #604](https://github.com/MGYamada/Vastitas/issues/604)) adds
[smooth affine declarations](language/smooth-declarations.md): smooth maps,
covectors and vectors at rational points, the metric-free reverse cotangent
pullback, and named metrics with checked evidence. Its
[acceptance map](stage3-acceptance.md) separates the same kinds of statement.

The book keeps four kinds of statement apart:

| Kind | Meaning |
| --- | --- |
| Implemented | The compiler accepts it and generates code for it. |
| Tested | A regression test in the repository exercises it. |
| Proved | A Lean theorem states it, under the assumptions listed in [Verification boundaries](verification.md). |
| Planned | A GitHub issue proposes it. It is not available yet. |

## How to read this book

Chapters 1 to 11 teach the language in order. They use programs from
[`examples/`](https://github.com/MGYamada/Vastitas/tree/main/examples) and the
test suite. Most chapters end with a short **What is checked** note that links
to the precise contract.

The later parts are references:

- **Vastitas Reference** gives the notation and the full contract for each
  language feature.
- **How the compiler is checked** describes the architecture, the wire protocols,
  the proof boundary and the standard-library admission rules.
- **Appendices** collect the CLI and diagnostics references, the independent
  reference models, the compiler limits, the historical roadmap with the Stage 1
  delivery records, the contributor checks and a glossary.

| Task | Where to start |
| --- | --- |
| Install the compiler and run a first program | [Getting Started](guide/getting-started.md) |
| Learn the language | [Values and functions](guide/values-and-functions.md) and the chapters that follow |
| Look up a precise rule | [Vastitas Reference](stage0.md) · [Wire protocols](protocol.md) |
| Inspect an implementation or proof claim | [Architecture](development/architecture.md) · [Verification](verification.md) · [Acceptance evidence](stage1-acceptance.md) |
| Look up a command, diagnostic or limit | [CLI](guide/cli.md) · [Diagnostics](appendix/diagnostics.md) · [Limits](appendix/limits.md) |
| Evaluate an independent reference model | [Reference models](appendix/reference-models.md) |
| Make a change | [Contributing and validation](appendix/contributing.md) |

Code blocks are labelled with their language: `vast` for Vastitas source, `sh`
for shell commands and `text` for output. Run commands from the repository root.

## Where the language goes next

Read [Historical Stages 2–7](guide/historical-roadmap.md). The roadmap follows
one line of development from the coordinate ring of an affine scheme to an
observable compared with physical measurements. Each stage has an example that
could establish completion and links to the issues that govern the current plan.

Copyright 2026 Vastitas Project Contributors.
[Apache License, Version 2.0](https://github.com/MGYamada/Vastitas/blob/main/LICENSE)
