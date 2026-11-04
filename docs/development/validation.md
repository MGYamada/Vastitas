# Validate the compiler and proofs

```sh
lake -d lean-kernel build vastitas-kernel
bash scripts/check_kernel_regressions.sh
cargo fmt --all -- --check
cargo clippy --locked --all-targets -- -D warnings
cargo test --locked --all-targets
python3 scripts/check_boundaries.py
```

To build the separate proof oracle and audit every kernel and oracle module
(the audit needs every kernel library root, executable and regression module
built first; it checks that each `.olean` exists, not that it is current):

```sh
lake -d lean-kernel build VastitasKernel VastitasPromotion VastitasPublicTest VastitasStorageTest VastitasAlgebraTest \
  vastitas-kernel storage-native-fixture numerical-native-fixture
bash scripts/check_kernel_regressions.sh
lake -d lean build VastitasOracle
(cd lean && lake env lean -DwarningAsError=true ../scripts/audit_axioms.lean)
lake -d lean env python3 scripts/check_axiom_audit.py
(cd lean && lake env lean -DwarningAsError=true ../scripts/check_oracle_core.lean)
(cd lean && lake env leanchecker VastitasOracle && lake env leanchecker VastitasKernel)
```

The last line replays every built Oracle and kernel module with the official
`leanchecker` against its imported environment, as CI does. It is not an
independent verifier, and it also reads stale `.olean` files left in `.lake`
by renamed modules, so run it on a clean build.

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
