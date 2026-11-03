# Vastitas

Vastitas compiles mathematical programs written in `.vast` to native executables.
Its finite Stage 1 compiler supports static functions and dispatch, nominal
affine geometry, scoped edit authority, checked storage ownership, real and
complex GEMM, and finite contraction trees. An independent Lean kernel
checks the program before generation. [Delivery record](docs/stage1-completion.md)

## Build and use

From the repository root with Rust 1.99.1, Lean 4.35.0 and a host C toolchain:

```sh
lake -d lean-kernel build vastitas-kernel
cargo build --locked
target/debug/vastitas check examples/pointed.vast
target/debug/vastitas build examples/pointed.vast -o target/pointed
./target/pointed
```

The program prints `42`. [Quick start](docs/guide/getting-started.md) ·
[CLI and diagnostics](docs/guide/cli.md) · [Packages and stdlib](docs/guide/stdlib.md)

## Documentation

Read the [English book](docs/README.md) or browse its [contents](docs/SUMMARY.md).
The [Stages 2–7 roadmap](docs/guide/historical-roadmap.md) follows current GitHub
issue decisions and distinguishes planned work from the delivered compiler.
[Build the book locally](docs/development/documentation.md)

**Fast like C** is the primary performance goal. Explicit layout and alias
checks, destination and scratch reuse, and visible allocation, packing and
retention costs govern the numerical design. Stage 2 or later owns controlled
Linux comparison with standalone C and outstanding tiny-call and total-cost
acceptance. [Storage and performance contract](docs/storage-ownership.md)

## Architecture

The Rust frontend supplies versioned input to the mathlib-independent Lean
kernel. Optional native storage and numerical runtimes link when the checked
entry needs them. [Compiler architecture](docs/development/architecture.md) ·
[Wire protocols 2–9](docs/protocol.md) · [Contributor guidance](AGENTS.md)

## Validation

The [validation guide](docs/development/validation.md) lists Rust, kernel,
oracle, native and CI checks. The [proof reference](docs/verification.md)
identifies the exact accepted inputs, conclusions and assumptions.

## License

Copyright 2026 Vastitas Project Contributors

Vastitas is licensed under the [Apache License, Version 2.0](LICENSE)
(`Apache-2.0`). This covers the project's compiler, runtime, Lean proofs,
standard library, examples, and documentation, except where otherwise noted.

Third-party dependencies and toolchain components retain their own licenses
and notices. Redistributing them requires preserving their applicable license
texts and attribution notices; this repository's license does not replace
those terms.
