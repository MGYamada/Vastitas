# Validate the compiler and proofs

```sh
lake -d lean-kernel build vastitas-kernel
bash scripts/check_kernel_regressions.sh
cargo fmt --all -- --check
cargo clippy --locked --all-targets -- -D warnings
cargo test --locked --all-targets
python3 scripts/check_boundaries.py
python3 scripts/check_spec.py
python3 scripts/check_primitive_table.py
```

`src/primitive_table.rs` is generated from the kernel's primitive families
(`lean-kernel/VastitasKernel/IndexedPrimitiveFamilies.lean`).
`check_primitive_table.py` builds that module, renders the table and fails on
any difference. After a change to the families, run
`python3 scripts/check_primitive_table.py --write` and review the diff of the
table.

To build the separate proof oracle and audit every kernel and oracle module
(the audit needs every kernel library root, executable and regression module
built first; it checks that each `.olean` exists, not that it is current):

```sh
lake -d lean-kernel build VastitasKernel VastitasPromotion VastitasPublicTest VastitasStorageTest VastitasAlgebraTest \
  vastitas-kernel storage-native-fixture numerical-native-fixture
bash scripts/check_kernel_regressions.sh
lake -d lean build VastitasOracle
(cd lean && lake env lean -DwarningAsError=true ../scripts/audit_axioms.lean)
(cd lean && lake env lean -DwarningAsError=true ../scripts/check_chain_rule_free.lean)
lake -d lean env python3 scripts/check_axiom_audit.py
(cd lean && lake env lean -DwarningAsError=true ../scripts/check_oracle_core.lean)
(cd lean && VASTITAS_SPEC_INPUT=../docs/spec/pins/oracle.json lake env lean -DwarningAsError=true ../scripts/spec_resolve.lean)
lake -d lean env python3 scripts/check_spec_lean.py
bash scripts/replay_lean.sh lean VastitasOracle
bash scripts/replay_lean.sh lean VastitasKernel
```

No library root imports `VastitasKernel.IndexedDescriptorExample`, the
definitions of the primitive that
[Add an indexed primitive](primitives.md#the-demonstration) demonstrates.
The regression `IndexedDescriptorRegression` and the oracle module
`IndexedDescriptorDemo` import it, so the regression script and the oracle
build both build it before the audit.

`check_spec.py` and `spec_resolve.lean` check the claims of the
[specifications](../specifications.md). After a change to the statement of a
cited theorem, review the change, run
`python3 scripts/check_spec.py --update-statements oracle` (or `bridge`) and
review the diff of the statement pins. After `(cd lean-bridge && lake build)`,
run the bridge resolver, a heavy check, with
`(cd lean-bridge && VASTITAS_SPEC_INPUT=../docs/spec/pins/bridge.json lake env lean -DwarningAsError=true ../scripts/spec_resolve.lean)`.

The last two lines replay every built Oracle and kernel module with the official
`leanchecker` against its imported environment, as CI does. It is not an
independent verifier, and it also reads stale `.olean` files left in `.lake`
by renamed modules, so run it on a clean build.

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
Regenerate them locally and commit them. For every example and manifest,
`scripts/capture_emit.py` records the wire request, the `check` and `emit`
responses and the generated Lean, and `--compare` reports every byte that
differs from an earlier capture. A change that promises identical generated
code, diagnostics or wire format runs it before and after.

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
([Appendix B](../appendix/diagnostics.md#output-format)), so no message may
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
replay, or `scripts/check_axiom_audit.py`.

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

Both Lean packages pin Lean v4.35.0. The oracle manifest contains only the
local kernel; Mathlib and its transitive packages are forbidden in both packages.
This build boundary preserves the separate mathematical-definition alignment
principle in [ADR 0001](../adr/0001-mathematics-first-stdlib.md#9-mathematical-alignment-and-oracle-dependency-independence).
CI runs Rust formatting and strict Clippy once, tests native compilation and
the arithmetic standard library on macOS and Linux with the oracle directory
absent, and builds/audits proofs without Mathlib in a separate job. On both
hosts, `audit-lean` runs the `nanoda_bin` from the pinned Lean toolchain. It runs on pull requests,
pushes to `main`, and manual dispatch; a pull request's branch pushes are checked once
through its `pull_request` run. Superseded runs for the same event and branch/PR are
cancelled; push and pull-request runs do not cancel each other.
Action revisions and language toolchains are pinned. CI installs elan 4.2.4
from a release archive whose SHA-256 is checked before its installer runs;
it does not execute elan's moving `master` bootstrap script. The isolated
installation does not modify shell profiles. Python is pinned to 3.15.2 and
checked without setup-python's extra loader path before native calibration;
unexpected loader overrides remain errors. Checkout credentials are not
persisted, and the external axiom auditor is
checked out at its exact commit in addition to the repository's own audit.
The optional OpenBLAS packing/workspace observations and the GEMM, tensor-packing
and contraction-tree experiment smokes run on pushes to `main` that touch their
source, harness and build inputs, and on manual dispatch. They do not run on pull
requests, so pull-request CI does not rebuild OpenBLAS for them; the required
compiler, proof and GEMM-adapter jobs continue to run on every pull request.

The dependency-boundary checker has its own regression tests:

```sh
python3 -m unittest discover -s scripts -p 'test_*.py'
```
