# Linux actual GEMM packing calibration

Measured clean feature commit `db62d224837031f1a8b3e05e6ca4756325716a04` in push
CI on 2026-11-01. All 26 repository inputs match that commit's actual Git blobs.
The measured identity is retained rather than replaced with a later publication
commit. This schema-2 record checks all 133 actual `(kernel,m,n,lda)` contracts,
including blocks up to 512 and strides outside the initial grid.
The [initial schema-1 record](https://github.com/MGYamada/Vastitas/blob/db62d224837031f1a8b3e05e6ca4756325716a04/experiments/openblas_packing/results/2026-11-01-linux/RESULTS.md)
remains available with its original measured test-merge identity and grid limitation.

The full [evidence archive](evidence.zip) and [manifest](artifact-manifest.json)
retain all 6,666 members. The ZIP is 6,685,652 bytes, SHA-256
`d6c6d8037ab8ef34b136def29e6894d5d61d159dd02b75e75782824c9a773072`.
It was downloaded from [successful job 124810850962](https://github.com/MGYamada/Vastitas/actions/runs/41293980212/job/124810850962),
[artifact 13078721542](https://github.com/MGYamada/Vastitas/actions/runs/41293980212/artifacts/13078721542).
The outer artifact ZIP was also checked against GitHub's recorded byte count
and digest before reading its two named evidence members.

The environment is Linux 7.0.0-1017-azure, x86_64, glibc 2.43, GCC 15.2.0.
The backend is pinned OpenBLAS 0.3.34, explicit HASWELL, sequential LP64,
with upstream-selected `NO_WARMUP`. This is shared CI, not a controlled timing
host. No operation timings or generated-source execution are claimed here.

## Checks and observations

- All 1,828 executions / 914 stock-diagnostic pairs passed complete output and
  input/padding checks against the independent integral oracle.
- Each of four direct-kernel binaries (stock/diagnostic, plain/sanitized harness)
  passed 8,464 cases and checked 55,961,496 output words. This configuration
  selects eight copy symbols, with D unroll 4/8 and Z unroll 4/2. Upstream
  kernel objects themselves are unchanged, not sanitizer-instrumented.
- All 133 observed shape/stride contracts additionally passed complete
  coordinate/input/guard checks on plain/sanitized stock/diagnostic binaries:
  532 direct footprint executions. The independent verifier reconstructs their
  exact coverage from the actual packing records and raw command receipts.
- Exactly 23 observer/CBLAS/GEMM-driver objects differ. All 769 kernel objects
  retain their stock hashes, including actual compute/copy and shortcut kernels.
- Diagnostic records contain 972 actual CBLAS routes: 828 packed GEMM and 144
  empty. No GEMV/small-matrix shortcut was observed in these cases on this
  configuration. This does not remove their explicit unmeasured status on other
  backends or workloads; macOS observes 48 GEMV routes in the same matrix.
- There are 385,254 actual packing calls, totaling 103,836,672 left-input and
  397,414,080 right-input logical packed payload bytes. All source, destination,
  active-pool and route checks passed.
- For `(2,50000,7)`, N/N overwrite packs the 112-byte real left input four times
  and the 224-byte complex left input twice: 448 logical bytes in either case.
  Right-input payload is 2,800,000 / 5,600,000 bytes. Different blocking explains
  different counts from macOS; no cross-machine speed comparison follows.
- The named declared pool metadata totals 4,484 bytes, including a 40-byte
  allocation mutex. The memory/release tables contain 3,200 / 1,200 bytes;
  three pointer/address fields and five flags/counters contain 24 / 20 bytes.
  Other backend data, linker padding, read-only tables and stack remain excluded.
- Observed pool capacity is 128 MiB, separate from actual logical packing.
  The packing observer declares 1,339,420 mutable bytes, separately from the
  163,869-byte workspace observer. These are diagnostic overhead, not stock costs.

All 29 unit/mutation/full-record tests passed in CI, and all 29 passed again
locally against the downloaded archive. The actual raw output and manifest were
independently replayed. Logical payload is not bus/cache traffic, RSS, peak memory
or a value to add to overlapping backing/capacity channels.

The [experiment contract](../../README.md) preserves the finite calibration,
instrumentation and trust boundaries. Source-lifecycle composition, shortcut
internals, complete backend/peak costs and the existing Fast like C timing gates
remain open. This record does not complete Stage 1 or establish native refinement.
