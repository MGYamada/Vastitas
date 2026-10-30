# Current C storage-copy baseline after PR #280

The benchmark was rerun against main
[`b66e6b370403cc9eaa860be796140aea5d5ae03a`](https://github.com/MGYamada/Vastitas/commit/b66e6b370403cc9eaa860be796140aea5d5ae03a)
after [#280](https://github.com/MGYamada/Vastitas/pull/280) merged at 16:19:30 JST
while the first report was being prepared. **All 200 cases passed output, source,
padding and paired resource-count checks.** The experiment remains a synchronous
C-copy baseline; it does not invoke or measure the new GEMM adapter.

The latest measurements do not establish C/C++ parity. Common lifecycle work
makes differences smaller, while some checked-copy results remain slower and
noisy. In particular, bulk real data with padded source and contiguous destination
(`p10/t00`) took **3.856 ms versus 3.189 ms** in the checked-call scope: a **1.209
ratio of the separate time medians**. The median of paired ratios is **1.111** with
within-run bootstrap interval **[0.998, 1.429]**. These statistics answer different
questions; neither is hidden or interpreted as a controlled-host acceptance result.

## Follow-up review and measurement scope

- #269 added affine resource calls; #271 connected the static package resource
  profile to protocol 8. Neither changed the native C files used in the first run.
- #280 added internal GEMM access helpers (`vstorage_prepare_dense`,
  `vstorage_prepare_write`, `vstorage_record_write`) and numerical status codes.
  The `prepare` function and the complete `copy_kernel`/`vstorage_copy` source
  remain byte-for-byte identical to #267. This benchmark adds no production API
  and does not use these newly added GEMM helpers.
- Main remained `b66e6b3` at the post-run check. The actual measured benchmark
  commit is [`6af3a3c6064d4cbac732f2cb9f784df1370e580d`](https://github.com/MGYamada/Vastitas/commit/6af3a3c6064d4cbac732f2cb9f784df1370e580d).
  The archive contains all measured C/Python sources and their hashes.
- The two runs have identical copy/baseline/prepared-wrapper assembly after
  normalizing assembler-local label names. This comparison does not equate
  binary addresses, whole-program layout, cache state or host conditions.
  The evidence archive contains `copy-path-equivalence.json` and full assembly.
- [The earlier run](../2026-10-30-epyc/RESULTS.md) is retained separately. Its
  largest checked-copy paired ratio was 1.124 for complex `p01/t11`; the same
  case is approximately 1.000 in this run. No samples are pooled or discarded,
  and changes between runs are **not attributed to #280**.

Only the C adapter and a matched C baseline are timed. The baseline shares the
exact allocation, preflight, alias/overflow, counter and cleanup machinery while
using a separately written conventional C copy loop. It is not an independent
safety implementation or a best-possible tiled transpose. See the
[full method and reproduction instructions](../../README.md).
No Lean FFI/generated execution/protocol-8 performance, GEMM, GPU or native
refinement is measured. This adds no `vastitas prof`, mandatory gate or completion
claim for #183 or #222.

## Procedure and coverage

- 30 October 2026, **16:29:36–16:35:30 JST**, AMD EPYC 9V74/KVM Linux x86-64,
  CPU 0 affinity, one thread, reported 32 MiB L3, glibc allocator. Shared virtual
  host activity and frequency were not controlled.
- GCC 13.3.0; `-std=c11 -O3 -Wall -Wextra -Werror -Wpedantic -fno-lto` for both
  separate translation units and linking. No fast-math, native-CPU flag, BLAS or
  timed sanitizer. Source/flags/environment and linked symbols are archived.
- 160 actual-copy cases: binary64/interleaved complex, source/destination
  independently contiguous or padded, four transpose combinations and logical
  sizes 0×7, 2×3, 16×17, 128×129 and 2048×2051. Another 40 cases are exact
  same-view self-copy. Empty/self cases have no element-loop result.
- Two warmup pairs, adaptive batching toward 5 ms, then 11 alternating-order
  measured pairs per scope. 528 case/scope groups; **11,616 measurement rows**
  and **18,870 raw rows** including calibration and warmups. No outlier removal.
- Reproduce: `python3 experiments/storage_copy/run.py --output /tmp/storage-copy-post280
  --samples 11 --target-ms 5 --no-leak-sanitizer`.

## Timings and dispersion

The following ranges cover the 32 bulk cases that actually copy data (16 real,
16 complex). These are case ranges, not a workload-weighted score.

| Scope | Ratio of separate time medians, adapter/C | Median of paired ratios, adapter/C |
|---|---:|---:|
| Lifecycle: allocate, initialize, preflight, copy, observe, cleanup | 0.919–1.063 | 0.936–1.041 |
| Checked call on reused buffers | 0.918–1.209 | 0.953–1.111 |
| Prepared loop only, reference | 0.922–1.142 | 0.975–1.178 |

Times below are median [Q25, Q75] per operation. `p10` means padded source and
contiguous target; `p01` means contiguous source and padded target. `t00` has no
transpose and `t11` transposes both views.

| Case | Scope | Adapter | C | Paired ratio [bootstrap 95%] |
|---|---|---:|---:|---:|
| Bulk real p00/t00 | Lifecycle | 32.071 [30.500, 34.273] ms | 31.616 [29.731, 32.817] ms | 1.021 [0.929, 1.104] |
| Bulk complex p00/t00 | Lifecycle | 61.516 [58.905, 67.175] ms | 62.809 [58.335, 66.231] ms | 1.032 [0.928, 1.077] |
| Bulk real p00/t00 | Checked call | 2.908 [2.716, 3.122] ms | 2.711 [2.621, 2.755] ms | 1.071 [1.009, 1.133] |
| Bulk complex p00/t00 | Checked call | 4.640 [4.408, 4.964] ms | 4.552 [4.520, 4.728] ms | 1.022 [0.957, 1.060] |
| Bulk real p10/t00 | Checked call | 3.856 [3.417, 4.428] ms | 3.189 [3.114, 3.803] ms | 1.111 [0.998, 1.429] |
| Bulk complex p01/t11 | Checked call | 34.837 [34.099, 36.182] ms | 35.015 [33.371, 36.946] ms | 1.000 [0.981, 1.028] |
| Bulk real p01/t01 | Loop only | 12.427 [12.082, 15.144] ms | 12.026 [11.181, 12.608] ms | 1.178 [0.963, 1.229] |
| Tiny real p00/t00 | Lifecycle | 153.31 [147.65, 163.23] ns | 145.80 [142.23, 149.82] ns | 1.068 [0.965, 1.153] |
| Tiny real p00/t00 | Checked call | 28.17 [26.25, 29.15] ns | 29.82 [27.47, 30.57] ns | 0.966 [0.860, 1.065] |

Small calls are reported in absolute nanoseconds; no tiny-call performance budget
is assigned. Lifecycle's shared fixture initialization can dominate the copy and
must not be used to infer prepared-loop parity. Prepared wrappers also have a
different compiler specialization context; their timings cannot be subtracted
from checked calls to isolate preflight cost.

The bulk-real self-copy checked call is separately **19.66 [18.90, 21.63] ns**
versus **20.11 [19.25, 20.44] ns** and moves **zero bytes**. It is not a bandwidth
result. Its lifecycle still allocates and initializes one large source buffer.

All intervals resample paired observations within this run. Host/process/toolchain
variation is not represented, and several intervals cross the provisional 1.10
bulk budget. No statistical pass/fail threshold is imposed.

## Costs and validation

For one contiguous bulk real lifecycle operation, both sides have 2 data
allocations and 2 frees, **67,207,168 peak data bytes**, **33,603,584 runtime
written/copied bytes** and **67,207,168 explicitly counted fixture initialization
bytes**. Complex doubles those data byte quantities. Runtime metadata uses 2
allocations and a 280-byte snapshot. Reused checked calls have zero timed data
or metadata allocations. Self-copy increments neither copy nor write counters.
Every batch ends with zero live data bytes; the raw file records exact totals
and repetition counts.

Exhaustive source/output/padding checks passed for every case, including special
IEEE bit patterns and independent complex components. The baseline boundary,
failure-before-write, overflow, alias, budget-cleanup and deliberately corrupted
oracle tests passed. Separate objects/no LTO, observable output checksums, and
retained assembly prevent silently erased copies.

ASan/UBSan, with `-fno-sanitize-recover=all`, passed the full 120-case small layout
matrix, contract/oracle tests and original `test_storage.c`. LeakSanitizer remains
disabled because the container cannot expose `/proc/.../task`; the
[original failure](../2026-10-30-epyc/initial-lsan-failure.json) is retained.
No LeakSanitizer success is claimed. Dependency boundaries, paired costs, artifact
roundtrips, local links and diff whitespace were checked. Lean, Rust and GEMM
tests/performance are not presented as part of this C-only experiment.

## Artifacts

- [Complete per-case summary](summary.md) and [machine statistics](summary.json.gz)
  retain medians, IQR, MAD, extrema, paired differences/ratios and intervals.
- [Raw CSV](raw.csv.gz) retains all phases and all counters.
- [Environment and revisions](environment.json) records toolchains, flags,
  source SHA-256 values, affinity, quotas and host snapshots.
- [Evidence archive](evidence.tar.gz) contains source snapshots, assembly,
  disassembly/symbols, build commands, sanitizer results, verification logs and
  unchanged-copy-path comparisons.
- [Artifact SHA-256 checksums](SHA256SUMS).

The earlier run remains available for transparency. The result is a reproducible
baseline with unresolved performance uncertainty, not closure of #183/#222 or a
claim about the full language execution path.
