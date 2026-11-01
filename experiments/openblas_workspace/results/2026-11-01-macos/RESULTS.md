# macOS workspace and backing observation

Measured clean revision: `cc42822f120c8792e7fa0747b509282dcd934dde`.
This is the feature revision before record publication and the subsequent
explicit 64-bit promotion of bounded fixture-size arithmetic. The archive retains
the exact measured sources; later code is not retroactively called measured.

The retained run contains **150 fresh-process executions / 75 stock–diagnostic
pairs**, three repetitions of the calibration and 24 adapter cases. The complete
75 diagnostic event streams, independent coordinate checks, stock agreement and
record inventory passed verification. All 16 repository source snapshots were
also compared against the measured Git commit, independently of the manifest.

Host: arm64 macOS 27.2, Apple clang 21.0.0. The actual backend reports
`OpenBLAS 0.3.34 NO_LAPACK NO_LAPACKE NO_AFFINITY USE_LOCKING VORTEXM4 SINGLE_THREADED`.
The diagnostic and stock builds have 1,741 object files; only
`driver/others/memory.o` differs. This is an **instrumented** backend observation,
not a stock allocator trace or performance measurement. No CPU affinity or
controlled-host claim is made.

| Observed channel | Calibration process | Each nonempty GEMM process |
|---|---|---|
| Pool buffer capacity | 33,554,432 bytes per buffer | 33,554,432 bytes |
| Peak simultaneous borrowed capacity | 67,108,864 bytes (two buffers) | 33,554,432 bytes (one buffer) |
| mmap capacity retained after all returns | 67,108,864 bytes | 33,554,432 bytes |
| Direct/no-lock malloc request | 33,558,528 bytes, then freed | None in this observed file |
| Final backing after explicit quit | Zero | Zero |
| Observer mutable storage | 163,869 bytes | 163,869 bytes |

Each of the 54 nonempty diagnostic GEMM processes maps once on its first call.
All three GEMM calls borrow and return the same capacity; the second overwrite
and accumulation add no backing request. Returning the buffer leaves its entire
mapping retained until quit. The 18 empty-case processes have no backing or pool
events. Rejected alias/invalid-mode preflight produces no backend event and
preserves all checked words. Output checksums canonicalize only computed zero
signs; input and padding words retain their bit checks.

Across all 75 diagnostic processes: 60 mmap requests and 60 unmaps; 171 pooled
borrows and returns; three direct borrows/returns with three malloc/free pairs;
75 shutdown begin/end pairs and 534 phase markers. No recorded allocation fails.
The complete summary groups only identical address-free observations and retains
every contributing case/repetition. These totals describe the test population,
not allocations for one source program.

Both actual memory compile commands include upstream `-DNO_WARMUP`. No phase-0
startup allocation or partial unmap occurs in this run. Partial-unmap handling is
tested by synthetic replay mutations, not calibrated by these live observations.
This run does not measure a warmup-enabled build. No small-matrix bypass is
inferred from the source option: the observed nonempty fixtures all borrow.

The mapping numbers are virtual ranges requested by the observed file, **not RSS,
committed/resident pages or actual packed matrix bytes**. Pool capacity overlaps
that backing. malloc requested bytes exclude allocator rounding/metadata and its
internal mappings. Arena data and the observer are separate channels. Other
OpenBLAS files, stack/local packing, general Lean allocations, generated-source
lifecycles and full process peaks remain unmeasured.

Reproduce verification without extracting or executing the ZIP:

```sh
python3 experiments/openblas_workspace/verify.py \
  experiments/openblas_workspace/results/2026-11-01-macos/evidence.zip
```

The [manifest](artifact-manifest.json) pins 518 members, 166 successful commands,
593,612 ZIP bytes and SHA-256
`02e68cd2cdcacdf18d54941f684fefaa43c07d29c12344b1d9bc397fa062047c`.
[`summary.json`](summary.json) is reproducible with the verifier's `--summary`
option. The [Linux record](../2026-11-01-linux/RESULTS.md) retains its own build and
different capacity; do not transfer this host's numbers to that backend.

No operation timing was recorded. The [full-cost and controlled-host Stage 1
gates](../../../../docs/stage1-completion.md) remain open.
