# Summary

[Vastitas](README.md)

- [Historical Stages 2–7](guide/historical-roadmap.md)

# Using the compiler

- [Build and run your first program](guide/getting-started.md)
- [CLI, native outputs and diagnostics](guide/cli.md)
- [Packages and the standard library](guide/stdlib.md)

# Language and packages

- [Core language and compatible geometry syntax](stage0.md)
- [Finite dispatch, abstract contracts and promotion](stage1a.md)
- [Independent functions and specialization](stage1b.md)
- [Packages, edit loans and transfer](packages.md)
- [Indexed declarations and the geometry library](indexed-source.md)

# Storage and numerical computing

- [Storage, ownership and residual retention](storage-ownership.md)
  - [Checked storage and resource calls](storage/checked-storage.md)
  - [Resource programs and runtime shapes](storage/resource-programs.md)
- [Numerical maps, ownership and GEMM](linalg/maps-and-gemm.md)
  - [Transforms, evaluation and metrics](linalg/transforms-and-metrics.md)
  - [Networks, packing and contraction trees](linalg/networks-and-packing.md)

# Implementation and verification

- [Compiler architecture](development/architecture.md)
- [Wire protocols 2–9](protocol.md)
- [Verification boundaries](verification.md)
  - [Pure evaluation and graph proofs](verification/core-models.md)
  - [Daleckii–Krein mathematical bridge](daleckii-krein.md)
- [Standard-library admission and trust](adr/0001-mathematics-first-stdlib.md)
- [Stage 1 delivery and performance handoff](stage1-completion.md)
  - [Finite-profile acceptance and evidence](stage1-acceptance.md)

# Reference models

- [Diagnostics, doctests and identifiers](reference/compiler-tools.md)
- [Analysis, certificates and random supplies](reference/analysis-and-effects.md)
- [Exact geometry reference models](reference/geometry.md)

# Contributing

- [Run compiler, proof and native checks](development/validation.md)
- [Maintain the documentation](development/documentation.md)
