# Run compiler, proof and native checks

This chapter lists the checks for a change to the compiler, the kernel, the
proofs or the native adapters. Each section gives the commands in the form
that the continuous integration (CI) runs, and
[What CI runs](#what-ci-runs) names the job of each. Run the commands from the
root of the repository. `AGENTS.md` says which checks each kind of change
needs, and [Maintain the documentation](documentation.md#build-check-and-preview)
gives the checks for a change to this book.

A check that passes is a test result. It is not a proof, and a report keeps
the two apart: state the commands that ran, their results and the checks that
did not run.

## Compiler and kernel

```sh
python3 scripts/check_docs.py
lake -d lean-kernel build vastitas-kernel
python3 scripts/check_boundaries.py
bash scripts/check_kernel_regressions.sh
bash scripts/check_indexed_native.sh
bash scripts/check_storage_native.sh
cargo fmt --all -- --check
cargo clippy --locked --all-targets -- -D warnings
python3 scripts/build_stdlib_package.py
cargo test --locked --all-targets
python3 scripts/check_resource_cleanup.py
python3 scripts/check_spec.py
python3 scripts/check_primitive_table.py
python3 -m unittest discover -s scripts -p 'test_*.py'
cargo package --locked
```

| Command | What it checks |
| --- | --- |
| `check_docs.py` | `AGENTS.md` and `CLAUDE.md` are identical and within their size limits |
| `check_boundaries.py` | The dependency boundaries: the kernel and the oracle do not depend on Mathlib. The bridge depends on the pinned Mathlib and, one way, on the kernel and the oracle, as the [amendment of ADR 0001](../adr/0001-mathematics-first-stdlib.md#implementation-correspondence-in-the-bridge-amendment-2026-11-12) admits. The packages share one Lean toolchain and keep their lockfiles. No `std` manifest depends on `nature`, as [ADR 0002](../adr/0002-nature-dimension.md) requires |
| `check_kernel_regressions.sh` | The regression modules that the script lists. Among others they cover the type audit, dispatch, function values, namespaces, edit authority, the indexed, affine, smooth, frame and physical-dimension checkers, the wire, storage, the numerical statements, exact algebra and promotion |
| `check_indexed_native.sh` | The code that the kernel generates from indexed Core: it compiles each generated module, runs it and compares its output |
| `check_storage_native.sh` | The native storage adapter and the cleanup after a failure, without BLAS |
| `cargo test --locked --all-targets` | The unit tests and the integration tests, which run `check` and `build` and the built executables. Build the kernel first |
| `check_resource_cleanup.py` | The cleanup of resource programs and the precedence of nested failures, without BLAS |
| `check_spec.py` | The files of the [specifications](../specifications.md) and their generated chapters |
| `check_primitive_table.py` | The generated primitive table, as described below |
| `unittest discover -s scripts` | The tests of the checkers and of the [reference models](../appendix/reference-models.md), among them `test_fixture_is_current` of `test_frame_reference.py`, which compares `tests/fixtures/frames.json` with the frame model |
| `cargo package --locked` | The registry distribution builds from its packaged sources |

`build_stdlib_package.py` generates the standard-library package under the
ignored directory `stdlib/target/package/`. With `--check` it compares that
directory with a fresh build instead of writing it.

`src/primitive_table.rs` is generated from the kernel's primitive families
(`lean-kernel/VastitasKernel/IndexedPrimitiveFamilies.lean`).
`check_primitive_table.py` builds that module, renders the table and fails on
any difference. After a change to the families, run
`python3 scripts/check_primitive_table.py --write` and review the diff of the
table.

After the build of the compiler, CI also runs two checks against it:

```sh
target/debug/vastitas audit-lean tests/fixtures/lean_audit/id_prop.ndjson
python3 -m unittest discover -s scripts -p 'test_diagnostic_reference.py' -v
```

The first runs the `nanoda_bin` of the pinned Lean toolchain on an exported
proof, as [Appendix A](../guide/cli.md) describes. The second runs the
[diagnostics model](../reference/compiler-tools.md#diagnostic-reference)
against the built compiler.

## Proof oracle and axiom audit

The oracle in `lean/` is a separate, proof-only package. The audit reads every
kernel and oracle module, so build every kernel library root, executable and
regression module first. The audit checks that each `.olean` exists, not that
it is current.

```sh
lake -d lean-kernel build VastitasKernel VastitasPromotion VastitasPublicTest VastitasStorageTest VastitasAlgebraTest \
  vastitas-kernel storage-native-fixture numerical-native-fixture
bash scripts/check_kernel_regressions.sh
lake -d lean build VastitasOracle
(cd lean && lake env lean -DwarningAsError=true ../scripts/audit_axioms.lean)
(cd lean && lake env lean -DwarningAsError=true ../scripts/check_chain_rule_free.lean)
(cd lean && VASTITAS_SPEC_INPUT=../docs/spec/pins/oracle.json lake env lean -DwarningAsError=true ../scripts/spec_resolve.lean)
bash experiments/iterator_prefix/check_lean.sh
bash scripts/replay_lean.sh lean VastitasOracle
bash scripts/replay_lean.sh lean VastitasKernel
lake -d lean env python3 scripts/check_axiom_audit.py
lake -d lean env python3 scripts/check_spec_lean.py
(cd lean && lake env lean -DwarningAsError=true ../scripts/check_oracle_core.lean)
(cd lean && lake env lean -DwarningAsError=true ../scripts/check_edit_acceptance.lean)
```

| Command | What it checks |
| --- | --- |
| `audit_axioms.lean` | The axioms and the opaque code of every kernel and oracle module |
| `check_chain_rule_free.lean` | The compiled reverse Core theorems that the specification states without the chain rule reach no chain-rule theorem |
| `spec_resolve.lean` | Each pinned oracle theorem and kernel definition of the specifications: its module, kind, axioms and statement hash |
| `experiments/iterator_prefix/check_lean.sh` | The Lean draft of the iterator-prefix experiment and its axioms |
| `replay_lean.sh` | Every built oracle and kernel module, a module whose name begins with `VastitasOracle` or `VastitasKernel`, replayed with `leanchecker` against its imported environment. The modules of `VastitasPromotion`, `VastitasPublicTest`, `VastitasStorageTest`, `VastitasAlgebraTest` and `Main` are not replayed |
| `check_axiom_audit.py` | The audit itself, on fixture packages that it must reject: its coverage, its provenance rules and substituted code |
| `check_spec_lean.py` | The resolver itself, on fixture claims |
| `check_oracle_core.lean` | The migrated Core proofs, on coordinate spaces, names and positional lists |
| `check_edit_acceptance.lean` | The indices of the finite edit acceptance |

The replay is not an independent verifier. It also reads stale `.olean` files
that renamed modules leave in `.lake`, so run it on a clean build. CI sets
`VASTITAS_REPLAY_THREADS=4` for these two replays;
[Memory budget for local verification](#memory-budget-for-local-verification)
gives the setting for a local run.

CI also builds the external axiom auditor `leanprover-community/axiom-audit`
at a pinned commit and runs it on `VastitasOracle` with the allowed axioms
`propext`, `Classical.choice` and `Quot.sound`. At the end of the job it
updates the Lake manifests, runs `check_boundaries.py` again and fails on a
manifest that differs from the committed one:

```sh
lake -d lean update
lake -d lean-kernel/native update
lake -d lean-kernel/numerical update
python3 scripts/check_boundaries.py
git diff --exit-code -- lean/lake-manifest.json lean-kernel/lake-manifest.json lean-kernel/native/lake-manifest.json lean-kernel/numerical/lake-manifest.json
```

No library root imports `VastitasKernel.IndexedDescriptorExample`, the
definitions of the primitive that
[Add an indexed primitive](primitives.md#the-demonstration) demonstrates.
The regression `IndexedDescriptorRegression` and the oracle module
`IndexedDescriptorDemo` import it, so the regression script and the oracle
build both build it before the audit.

## Specifications

`check_spec.py` and `spec_resolve.lean` check the claims of the
[specifications](../specifications.md). After a change to the statement of a
cited theorem, review the change, run
`python3 scripts/check_spec.py --update-statements oracle` (or `bridge`) and
review the diff of the statement pins.

## Frames and physical dimensions

A change to the frame runtime, to the frame or physical-dimension checks, to
the frame primitives or to `nature::dimension` runs these checks besides the
ones above:

```sh
python3 scripts/frame_reference.py --check
bash scripts/check_kernel_regressions.sh
bash scripts/check_indexed_native.sh
cargo test --locked --test frame_primitives --test frame_dimension_declarations \
  --test nature_dimension --test stdlib_frames --test emit_golden --test protocol_shape
python3 scripts/check_boundaries.py
python3 -m unittest discover -s scripts -p 'test_check_boundaries.py'
```

| Command | What it checks |
| --- | --- |
| `frame_reference.py --check` | The fixture `tests/fixtures/frames.json` is what the exact Python model of frames in the plane computes. `--write` regenerates it; review its diff |
| `check_kernel_regressions.sh` | Among its modules, `FrameRuntimeRegression` (the runtime on frames of the plane and of the point), `FrameDeclarationRegression` (frame declarations through the decoders, the source checker and the declaration audit), `NatureRegression` (the declarations of `nature::dimension` likewise), `FrameRegression` (the frame bindings through the checker, the Core semantics, erasure, code generation and the decoder) and `VastitasAlgebraTest.FrameReferenceRegression` (the runtime against the fixture of the reference model) |
| `check_indexed_native.sh` | The native fixture `frame_programs`, which links the frame runtime with the smooth and algebra runtimes and prints `42` |
| The Rust tests | The frame primitives through the public path and forged wire records; the frame and physical-dimension declarations and their protocol; `nature::dimension` and `std::geometry::frame` from path packages, with their public names and the byte identity of generated code without nature declarations; the generated Lean of the frame primitives; the unknown fields of every frame and physical-dimension record |
| `check_boundaries.py` and its tests | No `std` manifest depends on `nature`, and `nature` depends on nothing outside `std` and `nature` |

`scripts/test_frame_reference.py` tests the laws of the model itself:
adequacy, the transition laws, pairing invariance, the map arrays in two
frame pairs, the chain rule in frames and Gram transport. The model takes its
map arrays from the Jacobian, unlike the kernel, which takes them from runs
of the reverse pass.

## Mathematical bridge

The bridge in `lean-bridge/` is a separate package. It depends on the pinned
Mathlib and, one way, on the kernel and the oracle. Its workflow runs for a change to the bridge, to the kernel or oracle sources
that the bridge reads, or to the scripts below. For such a change run:

```sh
python3 scripts/check_boundaries.py
python3 -m unittest discover -s scripts -p 'test_check_boundaries.py'
(cd lean-bridge && lake exe cache get <modules>)
(cd lean-bridge && lake build)
(cd lean-bridge && lake env lean Audit.lean)
(cd lean-bridge && VASTITAS_SPEC_INPUT=../docs/spec/pins/bridge.json lake env lean -DwarningAsError=true ../scripts/spec_resolve.lean)
bash scripts/replay_lean.sh lean-bridge -v VastitasBridge
```

`lake exe cache get` fetches the Mathlib cache before the build. `<modules>`
is the list of Mathlib modules in the step "Fetch only the required Mathlib
cache" of the
[bridge workflow](https://github.com/MGYamada/Vastitas/blob/main/.github/workflows/lean-bridge.yml).
`Audit.lean` audits every bridge declaration and its transitive axioms. CI
sets `LEAN_NUM_THREADS=2` for the job and `VASTITAS_REPLAY_THREADS=2` for the
replay. At its end the job runs
`check_boundaries.py` again and fails on a Lake manifest that differs from the
committed one. Each of the last four commands is a heavy check: read
[Memory budget for local verification](#memory-budget-for-local-verification)
first.

## Numerical adapters

The numerical checks need the pinned sequential LP64 OpenBLAS 0.3.34.
`<prefix>` is the directory of that installation and `<output>` a directory
for the records of the C baselines.

```sh
python3 scripts/build_openblas.py --prefix <prefix> --jobs 4
python3 scripts/check_gemm_native.py --prefix <prefix>
python3 scripts/check_plain_c_baselines.py --prefix <prefix> --output <output> --no-leak-sanitizer
lake -d lean-kernel build vastitas-kernel storage-native-fixture
python3 scripts/check_gemm_checked.py --prefix <prefix>
OPENBLAS_NUM_THREADS=1 VASTITAS_TEST_OPENBLAS_PREFIX=<prefix> \
  cargo test --locked --test examples --test numerical_source --test tensor_source --test tree_source \
  --test cached_packing --test diagonal_metrics --test runtime_shape_source -- --ignored
```

These are the commands of the macOS job. The Linux job differs in five
places:

- `build_openblas.py` takes `--target HASWELL`, a supported CPU target;
- `check_gemm_native.py` takes `--valgrind`;
- `check_plain_c_baselines.py` takes `--valgrind` in place of
  `--no-leak-sanitizer`;
- `check_gemm_checked.py` takes `--lean-cc cc`;
- the `cargo test` step sets `VASTITAS_TEST_NATIVE_CC=cc`.

| Command | What it checks |
| --- | --- |
| `check_gemm_native.py` | The optional GEMM adapter: sanitizers, the ABI and, with `--valgrind`, uninitialized memory |
| `check_plain_c_baselines.py` | The standalone C baselines: their output, their cost records and their cleanup after a failure. It is no performance acceptance |
| `check_gemm_checked.py` | The checked GEMM schedules through the Lean FFI, and the cleanup of the generated native code |
| `cargo test … -- --ignored` | The tests that build and run programs with a matrix product, among them the numerical packages of this book in `--test examples` |

Between these steps the job calibrates three observations of the Lean
allocator, without timing: `experiments/stock_allocation_capabilities`,
`experiments/lean_allocation_diagnostic` and
`experiments/lean_allocation_lifetimes`. Each has a `run.py` and a
`verify.py`, and the workflow gives their arguments.

## Experiment harnesses

The job of the formatting and lint checks also runs the tests of the
experiment harnesses and verifies one retained record:

```sh
python3 -m unittest discover -s experiments/source_workspace -p test_fetch.py
python3 -m unittest discover -s experiments/contraction_trees -p 'test_*.py'
python3 -m unittest discover -s experiments/allocation_audit -p 'test_*.py'
python3 -m unittest discover -s experiments/stock_allocation_capabilities -p 'test_*.py'
python3 -m unittest discover -s experiments/lean_allocation_diagnostic -p 'test_*.py'
python3 -m unittest discover -s experiments/lean_allocation_lifetimes -p 'test_*.py'
python3 -m unittest discover -s experiments/runtime_shapes -p 'test_*.py'
python3 -m unittest discover -s experiments/iterator_prefix -p 'test_*.py'
python3 experiments/allocation_audit/verify.py experiments/allocation_audit/results/2026-11-01-macos-production/evidence.zip
```

## Pinned generated code

`tests/emit_golden.rs` compares the Lean that the kernel emits for a fixed
set of packages with `tests/fixtures/emit/*.lean`. Together those packages
declare every wire primitive and lower each one from an entry point. The test
asserts that they declare every wire primitive. It also asserts that the
generated Lean contains the lowering of each primitive except `relative_view`.
The lowering of `relative_view` is its operand, so the test has no text to look
for, and only the bytes of `tests/fixtures/emit/relative-view.lean` pin it. A
change to code generation must regenerate the fixtures and review their diff:

```sh
VASTITAS_UPDATE_EMIT_FIXTURES=1 cargo test --locked --test emit_golden
```

When `CI` is set, the test fails instead of regenerating the fixtures.
Regenerate them locally and commit them.

The frame primitives have a package of their own,
`tests/emit_corpus/frame-primitives/`, which `FRAME_CASES` of the same file
lists with its fixture `tests/fixtures/emit/frame-primitives.lean`.
`frame_lean_matches_the_emit_fixtures` compares its generated Lean and checks
that the package declares all thirteen frame operations and that the
generated Lean contains the lowering of each. `generated_lean_matches_the_emit_fixtures`
counts the frame package among the packages that together declare every
wire primitive. The command above regenerates both groups of fixtures; to
regenerate the frame fixture alone, name its test:

```sh
VASTITAS_UPDATE_EMIT_FIXTURES=1 cargo test --locked --test emit_golden -- frame_lean_matches_the_emit_fixtures
```

`scripts/capture_emit.py` records what the compiler emits for every example.
Its cases are the single-file programs under `examples/`, among them the
rejected programs of the book, and every package manifest under `examples/`,
`stdlib/` and `tests/emit_corpus/`. For each case it records the wire request,
the `check` and `emit` responses and the generated Lean. For a rejected
program or package of the book that the frontend rejects, it records the
diagnostics alone, because the frontend sends no request. `--compare` reports every byte that differs from an earlier capture.
A change that promises identical generated code, diagnostics or wire format
runs the script before and after, each time with the binaries of that tree:

```sh
python3 scripts/capture_emit.py --out <before> --kernel-fixtures
python3 scripts/capture_emit.py --out <after> --kernel-fixtures --compare <before>
```

CI does not run the capture.

The packages under `tests/emit_corpus/rejected/` reach the kernel and are
rejected there, so the capture also records the diagnostics of rejected
primitive calls. `tests/rejected_diagnostics.rs` pins those diagnostics in
every `cargo test` run. It checks that the frontend accepts each package,
runs `check` on it with the kernel and compares the exit code, the standard
output and the standard error with `tests/fixtures/rejected/<package>.txt`,
in the format of the capture's `cli.txt`. It fails on an expectation without
its package. A change to such a diagnostic must regenerate the expectations
and review their diff:

```sh
VASTITAS_UPDATE_REJECTED_FIXTURES=1 cargo test --locked --test rejected_diagnostics
```

As for the emit fixtures, the test refuses to regenerate when `CI` is set.

## Names in diagnostics

The kernel checks the headers of the declarations of a program under internal
symbols. A symbol encodes the canonical location of the declaring package as
decimal character codes. A message names a declaration by its name or its path
([Names and text in diagnostics](../language/diagnostics.md#names-and-text-in-diagnostics)),
so no message may
hold such a symbol. `assert_source_names` in `tests/common/mod.rs` fails on a
message that holds one, or a run of eight or more decimal numbers joined by
`_`. Every rejection that a test checks through `expect_code`,
`assert_first_code`, `assert_rejected` or `assert_wire_rejected` passes it. So
do the packages of the rejected corpus and the recorded rejections of the book.
`tests/diagnostic_names.rs` pins the message text of the dispatch and edit
diagnostics that name a declaration of a package.

## Memory budget for local verification

Run the heavy checks one at a time, and not while another process builds
Lean. A heavy check is the bridge build, `Audit.lean`, the bridge
specification resolver, `check_spec.py --update-statements`, a `leanchecker`
replay, `audit_axioms.lean`, or `scripts/check_axiom_audit.py`.

Always replay through `scripts/replay_lean.sh`. Do not call `leanchecker`
directly:

- `leanchecker` replays each target module as a separate task. Each task loads
  the whole import environment of its module.
- Lean runs the tasks on its worker pool. The pool has `LEAN_NUM_THREADS`
  threads, or one per core when the variable is unset.
- For bridge modules, each concurrent task holds its own copy of the imported
  Mathlib environment. On a 10-core machine an unset thread count therefore
  exhausts memory.
- `leanchecker` treats every argument that starts with `-` as a flag, so
  `leanchecker --help` names no module. Without a module, and outside a Lake
  package directory, it replays every module on its search path.

The script sets `LEAN_NUM_THREADS` from `VASTITAS_REPLAY_THREADS`, which
defaults to 1. It requires explicit module names, accepts only `-v` as a flag,
and reports a failed or killed replay as not verified.

```sh
bash scripts/replay_lean.sh lean-bridge -v VastitasBridge
```

The bridge replay was measured on 4 November 2026 with
`scripts/replay_lean.sh`'s settings. It ran on macOS arm64 with 16 GiB of
memory and Lean 4.35.0, against the Stage 3 S2 bridge. The default case was
stopped by a memory watchdog.

| `LEAN_NUM_THREADS` | Result | Wall time | Peak RSS |
| --- | --- | --- | --- |
| 1 | passed | 50 s | 2.65 GiB |
| 2 (the bridge CI setting) | passed | 38 s | 3.77 GiB |
| unset (10 workers) | killed after 7 s, when free memory fell below 25% | — | more than 6 GiB system-wide |

Other peaks on the same machine:

- `lake env lean Audit.lean` in `lean-bridge/`: about 3.4 GiB.
- `audit_axioms.lean`: about 4 GiB.
- Building one bridge module that imports Mathlib analysis: about 2.3 GiB.

Keep the sum of concurrent heavy checks below the free memory. With 16 GiB,
that means one heavy check at a time. This resolves
[#600](https://github.com/MGYamada/Vastitas/issues/600), where three
replays and audits ran at once.

## What CI runs

The workflows are in
[`.github/workflows/`](https://github.com/MGYamada/Vastitas/tree/main/.github/workflows).
The table names each job as its workflow does. In a job name, "host" stands
for the runner image of the job's matrix. The job of the documentation
workflow has no name, so the table gives its identifier.

| Workflow | Job | Hosts | Runs |
| --- | --- | --- | --- |
| CI, `ci.yml` | Rust formatting and lint | Linux | `check_docs.py`, `check_primitive_table.py`, `check_spec.py`, `cargo fmt`, `cargo clippy`, `cargo package`, the Python tests under `scripts/`, `check_boundaries.py`, the [experiment harnesses](#experiment-harnesses), and the generation and `--check` of the standard-library package |
| CI, `ci.yml` | Native compiler (host, no mathlib) | Linux and macOS | The kernel build, `check_boundaries.py` with the directory `lean/` absent, the three regression scripts, `cargo test --locked --all-targets`, `audit-lean`, `check_resource_cleanup.py` and the diagnostics model against the built compiler |
| CI, `ci.yml` | Optional GEMM adapter (host, OpenBLAS 0.3.34) | Linux and macOS | The commands of [Numerical adapters](#numerical-adapters) |
| CI, `ci.yml` | Lean proofs and axiom audit | Linux | The commands of [Proof oracle and axiom audit](#proof-oracle-and-axiom-audit), without Mathlib |
| Mathematical bridge, `lean-bridge.yml` | Daleckii–Krein proof and axiom audit | Linux | The commands of [Mathematical bridge](#mathematical-bridge) |
| Documentation book, `documentation.yml` | `book` | Linux | `mdbook build` with the pinned release and `scripts/check_book.py` |

- `ci.yml` and the documentation workflow run on pull requests, on pushes to
  `main` and on manual dispatch. A push to the branch of a pull request is
  checked once, through its `pull_request` run. The bridge workflow runs on
  pushes and pull requests that touch its paths, and on manual dispatch.
- In `ci.yml` and the bridge workflow, a later run for the same event and
  branch or pull request cancels the earlier one. Push runs and pull-request
  runs do not cancel each other.
- The workflows pin the revisions of their actions. `rust-toolchain.toml`
  pins Rust to 1.99.1, and every Lean package pins Lean v4.35.0. `ci.yml` and
  the OpenBLAS and experiment workflows pin Python to 3.15.2 with
  `setup-python`. The bridge workflow and the documentation workflow have no
  `setup-python` step: `check_boundaries.py` and `check_book.py` run there
  with the Python of the runner.
- CI installs elan 4.2.4 from a release archive and checks the SHA-256 of the
  archive before the installer runs. It does not execute elan's moving
  `master` bootstrap script, and the installation does not modify shell
  profiles.
- `scripts/check_ci_python.sh` checks Python without the extra loader path of
  `setup-python` before the native calibration. Another loader override is an
  error.
- A checkout does not persist its credentials.
- The observations of OpenBLAS packing and workspace, and the smoke runs of
  the GEMM, tensor-packing and contraction-tree experiments, have workflows of
  their own. They run on pushes to `main` that touch their inputs and on
  manual dispatch, not on pull requests, so pull-request CI does not rebuild
  OpenBLAS for them.

The oracle manifest contains only the local kernel, and Mathlib and its
transitive packages are forbidden in the kernel and in the oracle. This build boundary
preserves the separate mathematical-definition alignment principle in
[ADR 0001](../adr/0001-mathematics-first-stdlib.md#9-mathematical-alignment-and-oracle-dependency-independence).
