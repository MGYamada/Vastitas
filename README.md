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

**Fast like C is the primary performance and architecture goal.** Numerical
abstractions must support explicit layouts, checked aliasing, reusable destinations
and visible allocation/copy costs. The [storage and ownership design](docs/storage-ownership.md)
defines the contract and equivalent-C measurement gates; C-level performance has
not yet been established. Correctness and declared numerical semantics constrain
every optimization.

Stage 1a adds `generic`/`method` declarations with explicit callable domains,
nominal selectors and static capabilities. Lean checks all concrete keys for
ambiguity, every declared domain for coverage, and every applicable method
body before lowering calls to independently audited indexed Core. All public wire
versions now reach the same declaration/function/dispatch/authority checker;
[legacy source adaptation](docs/indexed-declarations.md#compatibility-adapter-for-protocols-26)
preserves existing input formats. The exact checked indexed Core has proved
terminating typed evaluation; [finite geometry migration](docs/geometry-migration.md)
records primitive result compatibility and the broader source/native proof limits. Stage 1b adds independent
lambdas, function values and higher-order specialization. This is not completion
of the full Stage 1 design. [Finite abstract scalar selectors](docs/abstract-types.md)
add nominal hierarchies and bodyless method contracts over the existing four keys.
[Scoped edit borrowing and validated assemblies](docs/edit-borrowing.md) permit owner-approved external contributions. [Nested reborrowing and permanent edit-authority transfer](docs/edit-authority.md) preserve function identity, grants and open obligations. Storage ownership and linear algebra remain pending in the [Stage 1 completion gate](docs/stage1-completion.md).

The [internal storage resource IR](docs/storage-ir.md) checks logical ownership,
loans, initialization and layouts with byte-region proofs. Its exact checked
schedule can generate native real/complex buffer operations with failure cleanup
and allocation/copy counters. [Internal resource functions](docs/storage-functions.md)
check owned arguments/results and borrowed destinations against actual caller
resources. [Protocol 8 resource functions](docs/resource-source.md) now connect
static storage schedules and pure return expressions to package source and native
execution. Dynamic shapes/value flow and end-to-end C performance comparisons
are still pending.
An [optional internal GEMM path](docs/numerical-adapter.md) checks resource access,
initialization and exact native lowering, then executes through pinned OpenBLAS.
[Numerical declaration profiles](docs/numerical-declarations.md) now independently
check ideal real/complex coefficients and nominal scalar bases through protocol 8.
The [protocol-8 numerical-value compiler](docs/numerical-values.md) checks local
nominal spaces, bases and loan-backed map products through actual GEMM lowering.
Public resource functions can use these operations; numerical builds require an
explicit `--openblas-prefix`, while ordinary compilation and `check` need no BLAS.
Dependent numerical inputs now preserve caller spaces/bases and borrow actual
map views under explicit static dimension contracts, including nested calls
and caller-selected output destinations. Initialized `OwnedMap` inputs/results preserve
those bases and their allocation/layout through ownership transfer.
[Typed transforms](docs/linear-transforms.md) add explicit dual/conjugate spaces,
corresponding bases, canonical involutions and adjoints for declared orthonormal
metrics, preserving views through nested calls. [Vector evaluation](docs/vector-evaluation.md)
adds bilinear dual evaluation and explicit Hermitian pairing through actual
borrowed vector arguments and scalar destinations. General metric realization,
generative numerical packages, dynamic shape/scalar
interfaces and networks remain pending.
GEMM also accepts explicit real/complex alpha/beta and synchronous reads from
initialized scalar loans, including coefficients computed by earlier operations.
This does not add general floating values to pure Core or dynamic shape contracts.

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

Storage and numerical builds coordinate access to their shared optional native
packages, including aliased paths. Waiting is interruptible; builds using only
the prebuilt pure runtime or independent optional packages can proceed concurrently. This
coordination adds no lock to generated programs. Keep direct `lake` builds or
package edits separate from compiler builds that use the same package artifacts.

The compiler uses this checkout's built backend and runtime. A relocatable
installation and cross-compilation are not provided. The optional
`VASTITAS_KERNEL` and `VASTITAS_KERNEL_ROOT` environment variables select a
trusted backend executable and kernel package directory for development.
The backend build includes the native runtime. `check` needs only the executable
when explicitly selected; `build` also needs the package and uses its pinned
`lean-toolchain` for the generated project.

### Internal Lean proof audit (v0.1.0 gate)

The Rust compiler also offers an opt-in, **non-authoritative** cross-check of
Lean proof exports using the pinned [`nanoda_lib`](https://github.com/ammkrn/nanoda_lib)
crate. Generate an NDJSON file with `lean4export`, then run:

```sh
cargo run --locked -- audit-lean path/to/lean4export.ndjson
```

`audit-lean` uses the checked-in [axiom-name policy](config/nanoda-internal-audit.json):
only the names `propext`, `Classical.choice`, and `Quot.sound` are allowed, with hard
rejection of all other exported axiom names. Their statements and dependencies
are not authenticated against the standard Lean environment. Every result is
explicitly conditional on the supplied environment and reports its exported
axiom count; renaming an arbitrary assumption does not validate it as a standard
Lean axiom. In particular, `sorryAx` and
`Lean.trustCompiler` are not permitted. The internal checker runs in an
isolated worker because rejection in upstream nanoda may panic or exit.

This command **rechecks an existing proof term**; it does not elaborate Lean
source, discover proofs, authorize `.vast` source/IR, or discharge any
constitutional theorem. The official Lean kernel remains the sole authority
for CI proofs, kernel compilation, and CS/MS/CF proof obligations. See
[the exact trust boundary](docs/verification.md#independent-internal-lean-export-audit-v010-gate)
and [v0.1.0 gate #282](https://github.com/MGYamada/Vastitas/issues/282).

## Path packages and modules

Use an explicit `Vastitas.toml` with required `[package]` name, SemVer version
and root source, plus optional `[dependencies]` path entries. Package mode
retains namespaces in protocol 3 (protocol 4 for abstract declarations, protocol 5 for edit assemblies, protocol 6 for delegated loans/transfers, protocol 7 for indexed declarations) and cannot be mixed with positional input or
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
| `lean/` | Proofs about the actual kernel definitions | Local kernel and Lean distribution only; no mathlib |
| `stdlib/src/` | Standard library written in `.vast` | Explicitly included `.vast` sources |

Ordinary compilation and generated programs do not call the proof oracle.
On the retained legacy Core path, the oracle proves Stage 0 checker soundness, source-to-core
correspondence, terminating typed evaluation, and runtime endpoint preservation.
It also proves the finite dispatch checker's unique selection, coverage, and
declaration-order invariance, and connects the retained Stage 1b checker's exact
lowered result to that proved core. Independent capture and static function
signature audits are connected to actual acceptance. Protocol-3 owner uniqueness,
reference/visibility and method-authority audits connect the namespace path to
the same core theorems. Protocols 5/6 also audit grant origins, exclusive loan transitions, complete contribution bodies and final winning footprints; protocol 6 additionally audits nested delegation and current-owner histories. Their exact assembled surfaces enter that same checker. Rust parsing, JSON decoding, full Stage 1
source rewriting correspondence, native code-generation equivalence, and a
full mathematical model of schemes remain outside those claims. The precise
[proof boundary](docs/verification.md) is part of the implementation contract.

The internal declaration-driven source adapters now compose independent
functions, finite scalar dispatch and edit-authority assemblies, including
applied and unapplied contribution bodies. [Public protocol 7](docs/indexed-source.md)
connects the Rust declaration/body syntax to that same combined checker and
returned Core. Legacy geometry syntax in protocol 7 uses the library’s explicit,
independently checked compatibility export. `IndexedProgramSafety` proves finite
typed evaluation for all functions and main in the exact returned Core, including
dependent calls and package openings. Finite geometry primitive results agree
with the retained runtime after erasure. Full source operational correspondence
and native refinement remain unproved. See
[indexed declarations](docs/indexed-declarations.md).

The [geometry standard library](stdlib/src/geometry/README.md) exposes
`std::geometry::scheme` and `std::geometry::smooth` for the existing affine
descriptors, nominal points, morphisms and existential packages. Use the
`stdlib` dependency entrypoint for geometry and arithmetic together. Original
legacy geometry clients use the same declaration identities in that package
closure; the temporary `stdlib/indexed` entrypoint has been removed.
The new declarations use the same protocol-7 checker as application declarations,
without privileges from geometric names. General scheme/manifold mathematics,
new geometric constructions and the rest of #211 remain future work.

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
lake -d lean build VastitasOracle
(cd lean && lake env lean ../scripts/audit_axioms.lean)
(cd lean && lake env lean ../scripts/check_oracle_core.lean)
```

Both Lean packages pin Lean v4.35.0. The oracle manifest contains only the
local kernel; Mathlib and its transitive packages are forbidden in both packages.
This build boundary preserves the separate mathematical-definition alignment
principle in [ADR 0001](docs/adr/0001-mathematics-first-stdlib.md#9-mathematical-alignment-and-oracle-dependency-independence).
CI runs Rust formatting and strict Clippy once, tests native compilation and
the arithmetic standard library on macOS and Linux with the oracle directory
absent, and builds/audits proofs without Mathlib in a separate job. It runs on pull requests,
pushes to every branch, and manual dispatch. Superseded runs for the same event
and branch/PR are cancelled; push and pull-request runs do not cancel each other.
Action revisions and language toolchains are pinned.

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
- [Indexed Core, runtime semantics and internal declaration/function/dispatch/authority elaboration](docs/indexed-declarations.md)
- [Compiler protocol](docs/protocol.md)
- [Identifier ASCII round-trip reference and integration contract](docs/identifier-ascii-reference.md)
- [Finite random-supply, exact-law, and logical-address reference](docs/rand-reference.md)
- [Arithmetic library](stdlib/README.md)
- [Proof scope and trust boundary](docs/verification.md)
- [Exact SOS real-cover reference and pending proof obligations](docs/sos-reference.md)
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
