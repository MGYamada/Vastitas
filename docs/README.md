# Introduction

*A Language for Math 2.0 and Physics 2.0.*

Vastitas compiles mathematical programs written in `.vast` to native
executables. A Rust frontend reads the source. An independent Lean kernel
then checks the whole program before any code is generated. This book
teaches the language, states its rules and says what backs each statement
about the compiler.

## Who this book is for

This book is for two kinds of reader:

- people who want to write and run `.vast` programs;
- contributors who need to know what the compiler checks and what it does
  not.

The first chapters assume some experience with a typed programming language.
The geometry and numerical chapters use some linear algebra and algebraic
geometry, and each chapter explains what it needs.

## Design goals

Vastitas has five design goals. Each names the language that sets the
standard for one side of the design:

- Syntax like Rust
- Experience like Julia
- Philosophy like Haskell
- Verification like Lean
- Performance like C/C++

The goals are aims. They say where the design is heading, and they are not
claims about what exists. [What exists today](#what-exists-today) says what
the compiler does and what backs it.

**Fast like C** is the name of the performance goal, and it has the highest
priority among the design goals. It names a C/C++-class target. A
mathematical abstraction must admit native code with the storage access,
the allocation behavior and the numerical kernel calls of a competent C
implementation of the same computation. The goal constrains the design from
the start. It asks for explicit layouts and aliases, for destinations and
scratch space that a caller supplies and reuses, and for visible costs of
allocation, packing and retention. Fast like C does not assert that programs
reach the performance of C, and its acceptance on a controlled host is open.
[Storage and ownership](storage-ownership.md#fast-like-c) states the goal
and its rules.

## Principles

Four principles run through the book:

- **Check before generating.** The kernel trusts no name and no annotation
  of the frontend. It resolves every name, assigns every identity and checks
  every body itself, including a body that no call reaches. `vastitas build`
  generates an executable only from a program that the kernel accepts.
  [Check before generating](language/guarantees.md#check-before-generating)
- **Mathematical identity is nominal.** Two spaces with equal dimensions are
  still different spaces, and a point remembers the object that it lies on.
  [Nominal identity](language/guarantees.md#nominal-identity)
- **Nothing implicit.** No value converts implicitly from one number type to
  another. Numerical and storage operations never insert a conjugation, a
  metric, a copy or an allocation for you.
  [Nothing implicit](language/guarantees.md#nothing-implicit)
- **Bounded and finite.** Every function of an accepted program ends. The
  compiler has fixed limits on the size of a program and on the work of
  checking it. It rejects a program beyond a limit and never accepts a part
  of one. The limits do not bound the time or the memory of a check.
  [Termination](language/guarantees.md#termination) ·
  [Limits](language/limits.md)

## What exists today

The repository holds the compiler, the standard library in `stdlib/` and
the programs in `examples/`. The book keeps four kinds of statement about
them apart:

| Kind | Meaning |
| --- | --- |
| Implemented | The compiler accepts it and generates code for it. |
| Tested | A regression test in the repository exercises it. |
| Proved | A Lean theorem states it, under the assumptions listed in [Verification boundaries](verification.md). |
| Planned | A GitHub issue proposes it. It is not available yet. |

Every part of the language in the next table is Implemented and Tested: the
compiler builds programs of that part, and the tests of the repository run
them. The tests that call a matrix product run in the numerical jobs of the
continuous integration, with the pinned OpenBLAS library. The table says what is Proved about each part. The linked
sections state the theorems and their assumptions, and this summary adds
nothing to them.

| Part of the language | Guide | Proved |
| --- | --- | --- |
| Functions, integers, pairs, dispatch, abstract types and function values | Chapters 2 to 5 | In the kernel's evaluator, every function of the Core that the kernel builds from a checked program ends with a value of its result type. The method that a call selects does not depend on the order of the methods. [Evaluation](verification.md#indexed-term-function-and-checked-program-evaluation) · [Dispatch](verification.md#stage-1a-finite-dispatch-and-checker-composition) |
| Packages, modules and edit authority | Chapters 1 and 6 | Each grant, delegation and transfer that the checker records for an accepted program is issued by the module that declares it, and its recipient is the module that the declaration names. [Current public checker routes](verification.md#current-public-checker-routes) |
| Indexed declarations and the geometry library | Chapter 7 | Evaluation preserves the type of a value, and in that type a point and a morphism keep both of their objects. [Evaluation](verification.md#indexed-term-function-and-checked-program-evaluation) |
| Presented affine geometry over the rational numbers | Chapter 8 | Two polynomials that the compiler finds equal are the same function. A declared fiber product has the universal property of a fiber product, and a declared open subset is the localization of its object. [Presented affine geometry](verification.md#presented-affine-geometry) · [Acceptance record](stage2-acceptance.md) |
| Smooth affine geometry with rational coefficients: polynomial smooth maps, covectors and vectors at rational points, reverse pullbacks, and named metrics with checked evidence. The kernel compiles each reverse pass that it can read and checks the result again | Chapter 9 | The chain rule for pullbacks, the agreement of the saved and the recomputing reverse pass, the comparison of the pullback with the derivative of real analysis, and the meaning of metric evidence. The theorems also state what each generated reverse function computes. That a whole compiled program agrees with its source is Tested, not Proved. [Smooth affine geometry](verification.md#smooth-affine-geometry-and-reverse-pullbacks) · [Acceptance record](stage3-acceptance.md) · [Compiled reverse passes](reverse-core-acceptance.md) |
| Storage and resource programs | Chapter 10 | Four facts about the model of storage that the checker keeps. Every access lies in its allocation. A read finds initialized bytes. Two active loans of which one writes do not overlap; a loan with a live child gives no access. An accepted entry point leaves no allocation and no loan. [Storage](language/guarantees.md#storage) · [What is outside these claims](verification.md#what-is-outside-these-claims) |
| Numerical maps: real and complex matrix products, transforms, metrics, tensor networks and contraction trees | Chapter 11 | The checked operations keep the objects and the bases of their maps, and the checker schedules a network or an evaluation with the conjugation flags of its operands. No theorem states a property of a floating-point result or of the BLAS library. [What is outside these claims](verification.md#what-is-outside-these-claims) · [Acceptance record](stage1-acceptance.md) |

Four limits hold for every row:

- That an executable computes what the checked program denotes is not
  Proved. The Lean compiler and the C compiler are trusted for it, and the
  tests that build and run programs exercise it.
- That the frontend sends the kernel the program that the source denotes is
  Tested, not Proved.
- The kernel builds its Core from the checked program. That this Core
  computes what the generics, the function values and the lambdas of the
  source denote is Tested, not Proved.
- A theorem about an accepted program is about the request that the kernel
  checks, or about the program that the kernel builds from it. No theorem
  is about the memory, the running time or the floating-point arithmetic of
  a machine.

[Guarantees](language/guarantees.md) states each guarantee of the language
with its evidence, and [Verification boundaries](verification.md) each
theorem with its assumptions.

Among the work that is Planned:

- The acceptance of Fast like C: the comparison of generated programs with
  a standalone C implementation of the same computation on a controlled
  host. [Performance evidence and acceptance](storage-ownership.md#performance-evidence-and-acceptance)
  states its conditions, and the
  [delivery record](stage1-completion.md#existing-performance-evidence-and-unresolved-gaps)
  lists the measurements that exist and their gaps.
- The later targets of the [roadmap](guide/historical-roadmap.md): bundles
  and tensor diagrams, spectral observations, a first physical model and
  the gluing of geometric objects.

[Specifications](specifications.md) record properties of the standard
library and of language constructs, apart from their code. Each claim about
a property has one of six
[claim statuses](specifications.md#claim-statuses). They keep Tested and
Planned and add Assumed and Not claimed. They divide Proved by where the
theorem lives: in the proof oracle or in the mathematical bridge, which uses
mathlib.

## How to read this book

The book has four parts.

The guide, chapters 1 to 12, teaches the language in order. Its complete
programs are files under
[`examples/`](https://github.com/MGYamada/Vastitas/tree/main/examples) that
the tests build and run. Many chapters have a note "What is checked", which
says what the compiler checks for the constructs of the chapter and what
backs it. A chapter ends with a See also list of the Reference sections that
hold its rules.

The Vastitas Reference states the rules of each construct. Its chapters
follow the guide:

| Chapter of the guide | Reference |
| --- | --- |
| 1. [Getting Started](guide/getting-started.md) | [Programs](language/programs.md) · [Packages](packages.md) |
| 2. [Values and functions](guide/values-and-functions.md) | [Lexical structure](language/lexical-structure.md) · [Items](language/items.md) · [Functions](language/functions.md) · [Statements](language/statements.md) · [Expressions](language/expressions.md) · [Types](language/types.md) |
| 3. [Control flow and pairs](guide/control-flow-and-pairs.md) | [Expressions](language/expressions.md) · [Types](language/types.md) |
| 4. [Generics, methods and dispatch](guide/dispatch.md) | [Generics and dispatch](stage1a.md) |
| 5. [Independent functions and specialization](guide/function-values.md) | [Function values](stage1b.md) |
| 6. [Packages, modules and edit authority](guide/modules-and-authority.md) | [Names and paths](language/names-and-paths.md) · [Modules](language/modules.md) · [Edit authority](language/edit-authority.md) |
| 7. [Indexed declarations and the geometry library](guide/indexed-geometry.md) | [Geometric types](language/geometric-types.md) · [Indexed declarations](indexed-source.md) |
| 8. [Presented affine geometry](guide/affine-geometry.md) | [Presented affine declarations](affine-geometry.md) |
| 9. [Smooth geometry and reverse pullbacks](guide/smooth-geometry.md) | [Smooth affine declarations](language/smooth-declarations.md) |
| 10. [Storage and resource programs](guide/storage.md) | [Storage and ownership](storage-ownership.md) · [Resource programs](storage/resource-programs.md) |
| 11. [Numerical maps, GEMM, metrics and tensor networks](guide/numerical.md) | [Numerical maps](linalg/maps-and-gemm.md) · [Transforms, evaluation and metrics](linalg/transforms-and-metrics.md) · [Networks, packing and contraction trees](linalg/networks-and-packing.md) |
| 12. [Diagnostics and the CLI](guide/diagnostics-and-cli.md) | [Diagnostics](language/diagnostics.md) · [Limits](language/limits.md) |

[Notation](language/notation.md) explains how the Reference writes syntax
and rules, and [Guarantees](language/guarantees.md) collects what holds for
every accepted program.

The part "How the compiler is checked" describes the
[architecture](development/architecture.md) of the compiler, its
[checking pipeline](internals/checking-pipeline.md), the
[wire protocols](protocol.md) between the frontend and the kernel, the
[proof boundary](verification.md) and the
[specifications](specifications.md).

The appendices hold the [commands](guide/cli.md), the
[diagnostic codes](appendix/diagnostics.md), the
[compiler limits](appendix/limits.md), the independent
[reference models](appendix/reference-models.md), the
[roadmap with the delivery records](appendix/history.md), the
[checks for contributors](appendix/contributing.md) and the
[glossary](appendix/glossary.md).

| Task | Where to start |
| --- | --- |
| Install the compiler and run a first program | [Getting Started](guide/getting-started.md) |
| Learn the language | [Values and functions](guide/values-and-functions.md) and the chapters that follow |
| Look up a rule | The Reference chapter of the construct, from the table above |
| Look up a command, a diagnostic code or a limit | [Appendix A](guide/cli.md) · [Appendix B](appendix/diagnostics.md) · [Appendix D](appendix/limits.md) |
| Look up a term | [Glossary](appendix/glossary.md) |
| Find what a guarantee rests on | [Guarantees](language/guarantees.md) · [Verification boundaries](verification.md) |
| Make a change to the compiler or the book | [Contributing and validation](appendix/contributing.md) |

Code blocks are labelled with their language: `vast` for Vastitas source,
`toml` for a manifest, `sh` for shell commands and `text` for output. Run
commands from the root of the repository.

## Where the language goes next

The [roadmap](guide/historical-roadmap.md) follows one line of development,
from the coordinate ring of an affine scheme to an observable that is
compared with physical measurements. Each of its steps has an example that
could establish completion, and links to the issues that govern the plan.

Copyright 2026 Vastitas Project Contributors.
[Apache License, Version 2.0](https://github.com/MGYamada/Vastitas/blob/main/LICENSE)
