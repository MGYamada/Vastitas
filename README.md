# Vastitas

Vastitas is a language for Math 2.0 and Physics 2.0. This repository implements
its **Stage 0 compiler**: `.vast` source → Rust frontend → independently checked
Lean IR → Lean/C → a native executable.

The current language supports exact integer computation and a small geometric
core. Ordinary and smooth affine descriptors, points, identity morphisms,
dependent arguments, and existential packages preserve nominal endpoints.
The [language design](docs/design.md) describes the larger research direction;
it is not a list of implemented features.

## Build and use

Requirements: Rust 1.99.1, Lean 4.35.0 via Elan/Lake, and a host C toolchain
(Xcode Command Line Tools on macOS or a C compiler on Linux).

```sh
lake -d lean-kernel build vastitas-kernel
cargo build --locked
cargo run --locked -- check examples/pointed.vast
cargo run --locked -- build examples/pointed.vast -o target/pointed
./target/pointed
# 42
```

`check` also accepts a library without `main`. `build` requires
`fn main() -> Int`; the generated entrypoint prints the integer and exits
successfully. Compilation never runs the generated program.

The compiler uses this checkout's built backend and runtime. A relocatable
installation and cross-compilation are outside Stage 0. The optional
`VASTITAS_KERNEL` and `VASTITAS_KERNEL_ROOT` environment variables select a
trusted backend executable and kernel package directory for development.

## Arithmetic standard library

The [arithmetic library](stdlib/README.md) contains `.vast` definitions for
`Int` and `Nat` addition, subtraction, multiplication, minimum and maximum,
plus integer negation and absolute value. Include the source files explicitly:

```sh
cargo run --locked -- build examples/stdlib-arithmetic.vast \
  --lib stdlib/src/arithmetic/int.vast \
  --lib stdlib/src/arithmetic/nat.vast -o target/stdlib-arithmetic
./target/stdlib-arithmetic
# 42
```

`--lib` also works with `check` and may be repeated. Libraries and the entry
file are checked together by Lean. Each file keeps its own diagnostic locations;
no implicit prelude or source-language import syntax is introduced.

## Architecture

| Directory | Responsibility | Dependencies |
| --- | --- | --- |
| `src/` | Rust CLI, parser, lexical resolution, versioned IR | Rust dependencies in `Cargo.lock` |
| `lean-kernel/` | Independent semantic checking, hygienic code generation, minimal runtime | Lean distribution only; no mathlib |
| `lean/` | Proofs about the actual kernel definitions | Kernel and pinned mathlib |
| `stdlib/src/` | Standard library written in `.vast` | Explicitly included `.vast` sources |

Ordinary compilation and generated programs do not call the proof oracle.
The oracle proves specific checker postconditions, geometric rules, and
preservation properties. It does **not** prove the entire parser, elaborator,
code generator, C compiler, or a full mathematical model of schemes correct.

## Validation

```sh
lake -d lean-kernel build vastitas-kernel
cargo fmt --all -- --check
cargo clippy --locked --all-targets -- -D warnings
cargo test --locked --all-targets
python3 scripts/check_boundaries.py
```

To build the separate proof oracle:

```sh
lake -d lean exe cache get
lake -d lean build VastitasOracle
```

The oracle manifest pins mathlib v4.35.0 and its transitive dependencies.
CI runs Rust formatting and strict Clippy once, tests native compilation and
the arithmetic standard library on macOS and Linux with the oracle directory
absent, and builds/audits proofs in a separate job. It runs on pull requests,
pushes to `main`, and manual dispatch. Superseded runs on the same branch/PR
are cancelled; action revisions and language toolchains are pinned.

The dependency-boundary checker has its own regression tests:

```sh
python3 -m unittest discover -s scripts -p 'test_*.py'
```

## Documentation

- [Stage 0 grammar, semantics, and limits](docs/stage0.md)
- [Compiler protocol](docs/protocol.md)
- [Arithmetic library](stdlib/README.md)
- [Proof scope and trust boundary](docs/verification.md)
- [Design v0.3, reorganized by topic](docs/design.md)
- [Contributor guidance](AGENTS.md)
