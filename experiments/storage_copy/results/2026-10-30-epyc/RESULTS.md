# Synchronous C adapter baseline — 30 October 2026

This is the earlier pre-#280 run. The [post-#280 refresh](../2026-10-30-epyc-post280/RESULTS.md)
contains the current baseline; both raw datasets are retained separately.

All 200 cases passed bitwise output/source/padding checks and matched allocation,
write and copy counters. Across the 32 **bulk cases that copy data** (16 real,
16 complex), median paired
adapter/C ratios ranged from **0.972–1.043 for lifecycle**, **0.941–1.124 for
checked calls**, and **0.955–1.136 for prepared loops**. Lifecycle includes common
allocation, initialization and cleanup costs and can conceal copy-loop differences.
These are case ranges from one shared virtual host, not an aggregate score,
acceptance decision, or C/C++ performance claim.

The largest checked-call ratio occurred for complex data with contiguous source,
padded destination and both views transposed: adapter **31.994 ms**, C **28.900 ms**;
the median of paired ratios was **1.124**, with within-run bootstrap interval
**[1.033, 1.171]**. That interval crosses #222's provisional 1.10 bulk budget, so
it does not establish a pass. It also does not establish a stable 12.4% regression
on a controlled host. The corresponding lifecycle ratio was 1.022, illustrating
why lifecycle and copy-call evidence must remain separate.

## Revision and scope

- Latest main checked before and after measurement:
  [`2d6a86ce4c8a44bd883d879035aa9c924ed8fc71`](https://github.com/MGYamada/Vastitas/commit/2d6a86ce4c8a44bd883d879035aa9c924ed8fc71).
- After [#267](https://github.com/MGYamada/Vastitas/pull/267),
  [#269](https://github.com/MGYamada/Vastitas/pull/269) added checked affine resource
  calls; [#271](https://github.com/MGYamada/Vastitas/pull/271) connected static
  package resources and pure returns to protocol 8. The entire `lean-kernel/native`
  directory is unchanged from merge `63d944ed67d96bfb8ad8183ddb5d7b1303c6c9ab`.
- The measured source is published at
  [`5daee61deb46cf92460b8870bcb62cf592985bed`](https://github.com/MGYamada/Vastitas/commit/5daee61deb46cf92460b8870bcb62cf592985bed).
  The environment records local measurement commit `228d378d98863b3f5669d978acc5598812c3544f`;
  these two commits have exactly the same source tree
  `358422510ee2938d225720fe35c4232234d724f2`. Archived sources and SHA-256 hashes
  independently identify the actual measured input.
- Only synchronous C adapter calls are timed. No Lean FFI, generated source
  execution, protocol-8 performance, GEMM, GPU, compiler latency or native
  refinement is measured. No production file/API, profiler or required gate changes.
  #183 and #222 remain open.

The [method](../../README.md) specifies the shared preflight/arena/accounting
contract and separately written conventional C loop. This baseline isolates loop
lowering under matched safety/lifecycle work; it is neither a separately designed
C runtime nor a best-possible tiled transpose or memcpy implementation.

## Host and procedure

- 30 October 2026, **16:08:40–16:14:19 JST** (timestamps also stored in UTC).
- AMD EPYC 9V74 virtual CPU, KVM, Linux x86-64, reported 32 MiB L3; pinned to CPU 0,
  one benchmark thread, glibc allocator. No cgroup throttling was recorded during
  this run. Host activity/frequency/turbo were not controlled, and small-call
  outliers are retained.
- GCC 13.3.0 (Ubuntu 13.3.0-6ubuntu2~24.04); `-std=c11 -O3 -Wall -Wextra -Werror
  -Wpedantic -fno-lto`, with separate driver/probe objects and no `-march=native`,
  fast-math or sanitizer in timed executables. No BLAS dependency or threading.
- 160 real-copy cases and 40 exact-self-copy cases. Five logical sizes: 0×7, 2×3,
  16×17, 128×129, 2048×2051; independent source/destination padding and all four
  transpose combinations. Each applicable scope uses two warmup pairs, adaptive
  batching and 11 measured pairs in alternating order. 528 case/scope groups,
  **11,616 measured batch rows**, **18,876 rows** including warmup/calibration.
- Reproduce with `python3 experiments/storage_copy/run.py --output /tmp/storage-copy-run
  --samples 11 --target-ms 5 --no-leak-sanitizer` on this restricted host.
  The current runner additionally makes UBSan diagnostics fatal; timed C sources
  and compilation flags are identical to the archived measured version.

## Representative results

Times are per operation, median [Q25, Q75]. `p00`: both contiguous;
`p01`: source contiguous/destination padded; `t00`: neither transposed;
`t11`: both transposed. Every ratio below is the **median of paired ratios**,
which need not equal the quotient of the two separate time medians.

| Case | Scope | Adapter | C | Paired ratio [bootstrap 95%] |
|---|---|---:|---:|---:|
| Bulk real p00/t00 | Lifecycle | 27.548 [26.895, 29.477] ms | 26.517 [25.949, 28.708] ms | 1.032 [0.995, 1.059] |
| Bulk complex p00/t00 | Lifecycle | 50.443 [49.892, 50.725] ms | 50.377 [49.854, 51.904] ms | 0.989 [0.962, 1.027] |
| Bulk complex p01/t11 | Lifecycle | 82.362 [80.726, 91.059] ms | 80.490 [78.675, 83.815] ms | 1.022 [1.005, 1.092] |
| Bulk real p00/t00 | Checked call | 2.367 [2.268, 2.572] ms | 2.383 [2.284, 2.514] ms | 0.941 [0.908, 1.123] |
| Bulk complex p00/t00 | Checked call | 4.367 [4.319, 4.531] ms | 4.596 [4.407, 4.769] ms | 0.972 [0.916, 1.006] |
| Bulk complex p01/t11 | Checked call | 31.994 [31.373, 32.737] ms | 28.900 [28.242, 30.082] ms | 1.124 [1.033, 1.171] |
| Bulk complex p01/t11 | Loop only | 31.868 [30.569, 34.305] ms | 29.113 [27.917, 29.609] ms | 1.136 [1.034, 1.173] |
| Tiny real p00/t00 | Lifecycle | 136.09 [131.71, 154.00] ns | 133.58 [131.18, 137.16] ns | 1.002 [0.970, 1.251] |
| Tiny real p00/t00 | Checked call | 25.51 [25.21, 26.15] ns | 24.72 [24.55, 25.52] ns | 1.020 [0.996, 1.047] |

For the bulk contiguous real/complex checked calls, payload-only effective rates
from the separate medians are approximately **13.22/14.33 GiB/s** for the adapter
and **13.13/13.62 GiB/s** for C. This divides logical payload bytes by elapsed
copy-call time; it is not measured DRAM bus traffic (which includes reads/writes,
write allocation, cache effects, and other traffic). The tiny real checked-call
median difference is about 0.80 ns; no tiny-call acceptance budget is assigned.

The separate bulk-real self-copy checked call takes 20.35 [19.62, 23.16] ns for
the adapter and 21.01 [19.86, 24.79] ns for C. It copies **zero bytes**. Its lifecycle
takes about 14 ms because it still allocates and initializes a large source buffer.
No self-copy or empty-case timing is interpreted as real-copy bandwidth.

## Resource and preservation evidence

For one bulk contiguous real lifecycle operation, both implementations allocate
and free 2 data buffers, peak at **67,207,168 bytes**, write/copy **33,603,584 bytes**
through the runtime and initialize **67,207,168 fixture bytes**. Complex doubles
these byte counts. Arena metadata uses 2 allocations and a 280-byte snapshot on
this host. Reused checked calls have **zero timed data/metadata allocations**.
Every cleanup leaves zero live data bytes; self-copy increments neither runtime
write nor copy counters. The raw rows retain batch totals and repetitions.

All logical words and all source/destination padding were checked bit-for-bit.
Special IEEE bit patterns and independent complex components are preserved.
Negative preflight, alias, overflow, budget-failure cleanup and intentional oracle
corruption checks passed. Separate object files/no LTO preserve repeated external
copy calls; generated assembly/disassembly retain the calls and actual copy loops,
and output checksums are observable.

ASan/UBSan passed the 120-case small matrix, baseline contract tests and unchanged
production `test_storage.c`. The final validation reran these with
`-fno-sanitize-recover=all`. **LeakSanitizer could not run**: its initial attempt
failed to read `/proc/.../task` in this container. Subsequent runs explicitly used
`ASAN_OPTIONS=:detect_leaks=0`. Zero-live-byte/free-count checks are reported, but
are not presented as a LeakSanitizer result. The dependency-boundary check and
diff whitespace checks passed. Lean/Rust/generated-program checks were not run:
those implementations are unchanged and are outside this C-only experiment.

## Retained artifacts

- [All case summaries](summary.md): per-case/scoped medians, IQR and paired intervals.
- [Machine summaries](summary.json.gz): also MAD, extrema, paired absolute differences,
  repetitions and minimum batch duration.
- [Raw CSV](raw.csv.gz): every warmup, calibration and measured sample; no outlier removal.
- [Environment](environment.json): compiler, flags, platform, affinity, source hashes,
  revision history, load and quota snapshots.
- [Evidence archive](evidence.tar.gz): actual C/Python source snapshot, assembly,
  disassembly, symbols, commands, sanitizer matrix and per-case verification log.
- [Final validation](final-validation.tar.gz): fatal-UBSan rerun and final runner source.
- [Initial LeakSanitizer failure](initial-lsan-failure.json): exact failed command and diagnostic.
- [Checksums](SHA256SUMS): SHA-256 hashes of these artifacts.

The statistical intervals concern within-run sampling only. They do not cover
different processes/hosts/toolchains, frequency policy, the Lean boundary, or
alternative C algorithms. Further controlled measurements and investigation of
the transposed complex case remain necessary before any performance acceptance.
