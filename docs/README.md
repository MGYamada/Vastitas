# Vastitas

Vastitas compiles mathematical programs to native executables. A Rust frontend
reads `.vast` source, and an independent Lean checker validates the program
before code generation. The finite Stage 1 compiler includes functions and
dispatch, ordinary and smooth affine geometry, storage ownership, real and
complex matrix multiplication, and checked tensor contraction trees.
[Stage 1 delivery and evidence](stage1-completion.md)

## Where the language goes next

Start with [Historical Stages 2–7](guide/historical-roadmap.md). The roadmap
follows one line of development from the coordinate ring of an affine scheme
to an observable compared with physical measurements. Each stage has an
example that could establish completion and links to the issues that govern
the current plan.

## Choose a reader path

| Task | Where to start |
| --- | --- |
| Compile a program, inspect a diagnostic or use `std` | [Quick start](guide/getting-started.md) · [CLI](guide/cli.md) · [Standard library](guide/stdlib.md) |
| Check a function, dispatch family, package or edit grant | [Core language](stage0.md) · [Dispatch](stage1a.md) · [Functions](stage1b.md) · [Packages](packages.md) |
| Use indexed geometry or numerical resources | [Indexed types](indexed-source.md) · [Storage contract](storage-ownership.md) · [Maps and GEMM](linalg/maps-and-gemm.md) |
| Inspect an implementation or proof claim | [Architecture](development/architecture.md) · [Protocols](protocol.md) · [Verification](verification.md) · [Acceptance evidence](stage1-acceptance.md) |
| Evaluate an independent reference model | [Compiler tools](reference/compiler-tools.md) · [Analysis and effects](reference/analysis-and-effects.md) · [Geometry](reference/geometry.md) |
| Make a change | [Validation](development/validation.md) · [Documentation maintenance](development/documentation.md) |

Copyright 2026 Vastitas Project Contributors.
[Apache License, Version 2.0](https://github.com/MGYamada/Vastitas/blob/main/LICENSE)
