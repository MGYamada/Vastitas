# Vastitas

Vastitas compiles mathematical programs written in `.vast` to native executables.
Its finite Stage 1 compiler supports static functions and dispatch, nominal
affine geometry, scoped edit authority, checked storage ownership, real and
complex GEMM, and finite contraction trees. An independent Lean kernel
checks the program before generation. [Delivery record](https://github.com/MGYamada/Vastitas/blob/main/docs/stage1-completion.md)
Historical Stage 2 adds a checked finite profile of presented affine geometry
over QQ. [Chapter](https://github.com/MGYamada/Vastitas/blob/main/docs/affine-geometry.md) · [Acceptance map](https://github.com/MGYamada/Vastitas/blob/main/docs/stage2-acceptance.md)
Historical Stage 3 adds a checked finite profile of smooth real affine geometry
over QQ: polynomial smooth maps, covectors and vectors at rational points, the
metric-free reverse cotangent pullback, and named metrics with checked evidence. [Reference](https://github.com/MGYamada/Vastitas/blob/main/docs/language/smooth-declarations.md) · [Acceptance map](https://github.com/MGYamada/Vastitas/blob/main/docs/stage3-acceptance.md)

## Build and use

From the repository root with Rust 1.99.1, Lean 4.35.0 and a host C toolchain:

```sh
lake -d lean-kernel build vastitas-kernel
cargo build --locked
target/debug/vastitas check examples/book/geometry/pointed.vast
target/debug/vastitas build examples/book/geometry/pointed.vast -o target/pointed
./target/pointed
```

The program prints `42`. [Getting started](https://github.com/MGYamada/Vastitas/blob/main/docs/guide/getting-started.md) ·
[CLI reference](https://github.com/MGYamada/Vastitas/blob/main/docs/guide/cli.md) · [Packages and manifests](https://github.com/MGYamada/Vastitas/blob/main/docs/guide/stdlib.md)

The [`examples/` conformance corpus](examples/README.md) indexes accepted
programs, package graphs, expected rejections and exact native outputs. Its
registry is checked in CI alongside the compiler's Rust and Lean regressions.

## Install the alpha

This alpha runs on macOS and Linux. Install Rust 1.99.1, Lean 4.35.0
(with Lake) and a host C toolchain. Cargo installs the driver. Build its
matching kernel in a writable directory and keep it for subsequent runs.

```sh
cargo install --locked --version '=0.1.0-alpha' vastitas
curl -fLsS https://static.crates.io/crates/vastitas/vastitas-0.1.0-alpha.crate -o vastitas-0.1.0-alpha.crate
tar -xzf vastitas-0.1.0-alpha.crate
cd vastitas-0.1.0-alpha
export VASTITAS_KERNEL_ROOT="$PWD/lean-kernel"
lake -d lean-kernel build vastitas-kernel
vastitas check examples/pointed.vast
vastitas build examples/pointed.vast -o pointed
./pointed
```

The published alpha archive predates the `examples/` corpus reorganization and
retains its historical flat paths; a main-branch checkout uses `examples/book/`.
The example prints `42`. Set `VASTITAS_KERNEL_ROOT` to this same absolute
path in each new shell. The first build that needs the storage or numerical
runtime compiles it inside that directory, so keep it writable. For programs
that import the combined standard library, run
`python3 scripts/build_stdlib_package.py` once in the extracted crate. The
optional `vastitas audit-lean` diagnostic needs Lean 4.35.0 installed by elan
and runs that toolchain's `nanoda_bin`.

Programs that run GEMM or diagonal Hermitian pairing also need sequential LP64
OpenBLAS 0.3.34, built with Python 3.12 or later, Make and the host C
toolchain. The 0.1.0-alpha crate does not ship the build script, so fetch it
from the release tag. On Linux, add `--native-cc cc` to the build command.

```sh
curl -fLsS https://raw.githubusercontent.com/MGYamada/Vastitas/v0.1.0-alpha/scripts/build_openblas.py -o build_openblas.py
python3 build_openblas.py --prefix "$PWD/openblas-0.3.34" --jobs 4
vastitas build --manifest-path examples/packages/numerical/Vastitas.toml \
  --openblas-prefix "$PWD/openblas-0.3.34" -o numerical
./numerical
```

[Numerical builds](https://github.com/MGYamada/Vastitas/blob/main/docs/guide/cli.md#numerical-builds) ·
[Adapter contract](https://github.com/MGYamada/Vastitas/blob/main/docs/linalg/maps-and-gemm.md#numerical-adapter)

## Documentation

Read the [English book](https://github.com/MGYamada/Vastitas/blob/main/docs/README.md) or browse its [contents](https://github.com/MGYamada/Vastitas/blob/main/docs/SUMMARY.md).
It starts with Getting Started and teaches the language chapter by chapter;
the Vastitas Reference, the verification boundaries and the appendices follow.
The [Stages 2–7 roadmap](https://github.com/MGYamada/Vastitas/blob/main/docs/guide/historical-roadmap.md) follows current GitHub
issue decisions and distinguishes planned work from the delivered compiler.
[Build the book locally](https://github.com/MGYamada/Vastitas/blob/main/docs/development/documentation.md)

**Fast like C** is the primary performance goal. Explicit layout and alias
checks, destination and scratch reuse, and visible allocation, packing and
retention costs govern the numerical design. Stage 2 or later owns controlled
Linux comparison with standalone C and outstanding tiny-call and total-cost
acceptance. [Storage and performance contract](https://github.com/MGYamada/Vastitas/blob/main/docs/storage-ownership.md)

## Architecture

The Rust frontend supplies versioned input to the mathlib-independent Lean
kernel. Optional native storage and numerical runtimes link when the checked
entry needs them. [Compiler architecture](https://github.com/MGYamada/Vastitas/blob/main/docs/development/architecture.md) ·
[Wire protocols 2–9](https://github.com/MGYamada/Vastitas/blob/main/docs/protocol.md) · [Contributor guidance](https://github.com/MGYamada/Vastitas/blob/main/AGENTS.md)

## Validation

The [validation guide](https://github.com/MGYamada/Vastitas/blob/main/docs/development/validation.md) lists Rust, kernel,
oracle, native and CI checks. The [proof reference](https://github.com/MGYamada/Vastitas/blob/main/docs/verification.md)
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
