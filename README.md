# Vastitas

Vastitas is a language for Math 2.0 and Physics 2.0. This repository implements
its **Stage 1b compiler with path packages, finite abstract selectors/contracts and scoped edit assemblies**: `.vast` source → Rust frontend → independently checked
Lean IR → Lean/C → a native executable.

The current language supports exact integer computation, a small geometric
core, finite multiple dispatch over scalar types, and capture-free static
higher-order functions, local path packages and call-only module imports. Ordinary and smooth
affine descriptors, points, identity morphisms,
dependent arguments, and existential packages preserve nominal endpoints.
The [language design](docs/design.md) describes the larger research direction;
it is not a list of implemented features.

Stage 1a adds `generic`/`method` declarations with explicit callable domains,
nominal selectors and static capabilities. Lean checks all concrete keys for
ambiguity, every declared domain for coverage, and every applicable method
body before lowering calls to the proved Stage 0 core. Stage 1b adds independent
lambdas, function values and higher-order specialization. This is not completion
of the full Stage 1 design. [Finite abstract scalar selectors](docs/abstract-types.md)
add nominal hierarchies and bodyless method contracts over the existing four keys.
[Scoped edit borrowing and validated assemblies](docs/edit-borrowing.md) permit owner-approved external contributions. [Nested reborrowing and permanent edit-authority transfer](docs/edit-authority.md) preserve function identity, grants and open obligations. Storage ownership and linear algebra remain pending in the [Stage 1 completion gate](docs/stage1-completion.md).

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

Build refuses an output path that aliases any input source, including an
explicit library, package manifest or module file. On macOS and Linux, SIGINT/SIGTERM cancel compiler children
and remove the temporary project and staging output. Existing output is kept
until the final atomic replacement. SIGKILL or a host crash cannot run cleanup.

The compiler uses this checkout's built backend and runtime. A relocatable
installation and cross-compilation are not provided. The optional
`VASTITAS_KERNEL` and `VASTITAS_KERNEL_ROOT` environment variables select a
trusted backend executable and kernel package directory for development.
The backend build includes the native runtime. `check` needs only the executable
when explicitly selected; `build` also needs the package and uses its pinned
`lean-toolchain` for the generated project.

## Path packages and modules

Use an explicit `Vastitas.toml` with required `[package]` name, SemVer version
and root source, plus optional `[dependencies]` path entries. Package mode
retains namespaces in protocol 3 (protocol 4 for abstract declarations, protocol 5 for edit assemblies, protocol 6 for delegated loans/transfers) and cannot be mixed with positional input or
`--lib`; protocol 2 remains supported for those existing commands.

```sh
cargo run --locked -- check --manifest-path examples/packages/demo/Vastitas.toml
cargo run --locked -- build --manifest-path examples/packages/demo/Vastitas.toml -o target/demo
./target/demo
# 42
```

`mod`, `use`, `as`, `pub`, `pub use`, `package::`, `self::` and `super::` support
logical modules and aliases. Functions have one defining package/module owner;
ordinary methods require that exact module; explicit grants and active assembly loans permit external contributions. Imports permit repeated calls
without granting edit authority. See [packages and modules](docs/packages.md)
for file layout, visibility, limits and proof scope. Registry/Git dependencies and
general abstract values remain deferred; explicit edit borrowing uses protocols 5/6.

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
this protocol-2 `--lib` mode has no implicit prelude or module/import syntax.
Use [manifest mode](docs/packages.md) for path packages and imports.

The generic `add` and `maximum` wrappers use the same prefixed functions:

```sh
cargo run --locked -- build examples/dispatch-arithmetic.vast \
  --lib stdlib/src/arithmetic/int.vast \
  --lib stdlib/src/arithmetic/nat.vast \
  --lib stdlib/src/arithmetic/generic.vast -o target/dispatch-arithmetic
./target/dispatch-arithmetic
# 42
```

Their domains are all four Nat/Int pairs. Mixed methods bind `promote` once and
delegate through its projections to the Int/Int method. Nat/Nat retains Nat.
Generic arguments determine selection, so bare literals choose Int.
There is no implicit conversion or selection using the expected result type.
See [the Stage 1a specification](docs/stage1a.md) for selectors, capabilities,
the 4096-key bound, and examples of ambiguity.

## Independent functions

```vast
fn invoke(f: Fn<Int, Int>, x: Int) -> Int { f(x) }
fn main() -> Int {
    let increment: Fn<Int, Int> = fn(x: Int) -> Int { x + 1 };
    invoke(increment, 41)
}
```

Function types use `Fn<Int, Int>`, `Fn<(Int, Int), Int>`, `Fn<(), Int>`,
or `Fn<Unit, Int>`; the last two distinguish zero arguments from one Unit
argument. Lambdas have explicit parameter/result types and cannot capture
outer locals. Named functions can also be passed, aliased, returned and called.
Lean resolves calls to a single static target and erases function values.
Generic families remain declarations, usable through ordinary wrappers.
See [Stage 1b](docs/stage1b.md) for the contract and proof boundary.

```sh
cargo run --locked -- check examples/functions.vast
cargo run --locked -- build examples/functions.vast -o target/functions
./target/functions
# 42
```

## Homogeneous pairs

Ordinary functions and selected methods support homogeneous `Pair<Nat>` / `Pair<Int>` values
through `pair`, `pair_first`, and `pair_second`. Their elements are inferred
without conversion; Pair is excluded from dispatch keys and Fn contracts.
See [the Pair contract](docs/stage1b.md#homogeneous-data-pairs) and
[native example](examples/pairs.vast). The stdlib's four-key `promote` preserves
Nat/Nat as Pair<Nat> and embeds mixed keys into Pair<Int> explicitly. See the
[promotion contract and package usage](stdlib/README.md#explicit-promotion).
The [numerical proof contract](docs/promotion.md) covers the actual checked
stdlib bodies; this increment does not complete the historical Stage 1 proposal.

## Architecture

| Directory | Responsibility | Dependencies |
| --- | --- | --- |
| `src/` | Rust CLI, parser, lexical resolution, versioned IR | Rust dependencies in `Cargo.lock` |
| `lean-kernel/` | Independent semantic checking, hygienic code generation, minimal runtime | Lean distribution only; no mathlib |
| `lean/` | Proofs about the actual kernel definitions | Kernel and pinned mathlib |
| `stdlib/src/` | Standard library written in `.vast` | Explicitly included `.vast` sources |

Ordinary compilation and generated programs do not call the proof oracle.
The oracle proves actual Stage 0 checker soundness, source-to-core
correspondence, terminating typed evaluation, and runtime endpoint preservation.
It also proves the finite dispatch checker's unique selection, coverage, and
declaration-order invariance, and connects the public Stage 1b checker's exact
lowered result to that proved core. Independent capture and static function
signature audits are connected to actual acceptance. Protocol-3 owner uniqueness,
reference/visibility and method-authority audits connect the namespace path to
the same core theorems. Protocols 5/6 also audit grant origins, exclusive loan transitions, complete contribution bodies and final winning footprints; protocol 6 additionally audits nested delegation and current-owner histories. Their exact assembled surfaces enter that same checker. Rust parsing, JSON decoding, full Stage 1
source rewriting correspondence, native code-generation equivalence, and a
full mathematical model of schemes remain outside those claims. The precise
[proof boundary](docs/verification.md) is part of the implementation contract.

## Validation

```sh
lake -d lean-kernel build vastitas-kernel
bash scripts/check_kernel_regressions.sh
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

- [Stage 0 core grammar, semantics, and limits](docs/stage0.md)
- [Stage 1a finite multiple dispatch](docs/stage1a.md)
- [Stage 1b independent functions](docs/stage1b.md)
- [Finite abstract scalar selectors](docs/abstract-types.md)
- [Packages and modules](docs/packages.md)
- [Implementation roadmap](docs/stage1-roadmap.md)
- [Post-Stage 1 docs cleanup and mdBook plan](docs/docs-cleanup-plan.md)
- [Scoped edit borrowing and assemblies](docs/edit-borrowing.md)
- [Nested edit loans and permanent authority transfer](docs/edit-authority.md)
- [Indexed Core, runtime semantics and internal declaration/type/body elaboration](docs/indexed-declarations.md)
- [Compiler protocol](docs/protocol.md)
- [Arithmetic library](stdlib/README.md)
- [Proof scope and trust boundary](docs/verification.md)
- [Design v0.3, reorganized by topic](docs/design.md)
- [Contributor guidance](AGENTS.md)

## License

Copyright 2026 Vastitas Project Contributors

Vastitas is licensed under the [Apache License, Version 2.0](LICENSE)
(`Apache-2.0`). This covers the project's compiler, runtime, Lean proofs,
standard library, examples, and documentation, except where otherwise noted.

Third-party dependencies and toolchain components retain their own licenses
and notices. Redistributing them requires preserving their applicable license
texts and attribution notices; this repository's license does not replace
those terms.
