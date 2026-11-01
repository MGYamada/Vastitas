# Full Linux tree run with the original coordinate-copy C baseline

Status: actual generated execution, native validation and paired cost records
passed. These are exploratory shared-host measurements, not performance acceptance.
The comparator's second regroup copies individual cells. Review found that its
common contiguous x axis permits a block copy. The stronger comparator now has a
[separate measured record](../2026-10-31-linux-block-copy/RESULTS.md). The favorable bulk ratios below cannot
establish performance against that stronger C implementation. This original run
is retained, including its unfavorable tiny/small results; it is not replaced or
attributed to later source.

## Revision and retained evidence

- [Successful run 41215383268](https://github.com/MGYamada/Vastitas/actions/runs/41215383268/job/124578705540).
- Measured clean commit: `69eafbee74ca7cbecea74824d25e65d931f51a7c`.
- Actual harness interval: 2026-10-31 15:35:51–15:40:42 UTC.
- Twelve canonical public check/build/executions and exact independent kernel
  check/emit/wrapper builds; two native builds per case (optimized and
  ASan/UBSan/LSan), with all coordinate/scratch/padding/mutation checks passing.
- 2,640 raw rows = 288 warmup + 768 calibration + 1,584 measurement rows:
  **1,320 generated/C pairs**, 72 case/scope groups, eleven measurement pairs
  per group. An additional 288 exhaustive generated/C verification executions
  ran outside timing. Native selftest records are also separate from timings.
- Compact original artifact `13048765297`: **418,479 bytes**, SHA-256
  `596a69ad396d60741d985fd0db75cf5c89bf2044c3c8d419f78fbebcf7cebcfa`.
  [evidence.zip](evidence.zip) retains all 170 members, including command logs,
  public packages/wire, exact generated Lean/wrappers and source snapshots.
  [artifact-manifest.json](artifact-manifest.json) lists member hashes and sizes.
- Large inspection artifact `13047927083`: 60,388,356 bytes, published SHA-256
  `7aa6cd1a1042cd5415259418d7fe3527590b8d49b8f8e0d3c8cadea507e7aa0c`.
  It was **not downloaded or independently content-audited** here. Its 24 symbol
  and disassembly files are identified by hashes/sizes in retained command logs;
  the twelve linked-library listings are in the compact archive. Both hosted
  artifacts expire 2026-11-14; the compact evidence is retained in this repository.

The repository also exposes [raw.csv](raw.csv), [summary.json](summary.json),
[summary.md](summary.md), [cases.json](cases.json), [environment.json](environment.json),
[native-validation.json](native-validation.json), [compile-times.json](compile-times.json),
[openblas-build.json](openblas-build.json) and [status.json](status.json).

## Host and comparison contract

AMD EPYC 9V74 Azure VM, four visible logical CPUs; the harness and children were
pinned to allowed CPU 0. Frequency, turbo and other VM/host activity were not
controlled. Linux 7.0.0-1017-azure, glibc 2.43, GCC 15.2.0, Rust 1.99.1 and pinned
Lean 4.35.0 were recorded. Load averages changed from `4.19 2.04 0.80` to
`1.55 1.67 0.98`.

Both sides use the same static sequential LP64 OpenBLAS 0.3.34 HASWELL archive,
SHA-256 `1ca3e930bb5e5ec46000ea7978e019abb3076d31eb56bc382b030ac46051fcaa`,
one thread, `NativeFast`, identical scalar/layout/padding and written
pack/GEMM/regroup/GEMM order. The C second regroup is the original cell-copy
loop; it uses the same coordinate mapping and byte traffic but misses the block
copy noted above. No production compiler or native runtime was changed by this
measurement.

Cases use `(i,k,j,a,b)` = tiny `(2,3,4,5,6)`, small `(7,17,5,11,13)` and bulk
`(24,40,32,48,56)`, each real/complex and contiguous/padded. Data are freshly
initialized and reused, with at most 2,825,248 simultaneously live arena bytes;
this is not a cold-cache/DRAM study. CPU and scope differences prevent attributing
changes versus earlier GEMM/tensor records to a compiler improvement.

## Exact costs and independent verification

Let `w` be 8 or 16, `P=w*i*k*j`, `R=w*i*j*a`, and `C=w*i*a*b`.
Every four-operation repetition writes `P+2R+C` bytes and copies `P+R` bytes.
Six allocations/frees are performed per lifecycle, and none in the reused timed
window. The scratch capacity is the maximum of both explicit packing footprints;
padding/offsets remain included in capacity. Lifecycle initialization additionally
writes all six capacities plus `w*(i*k*j+k*a+j*b+6)` bytes. Every output/cost pair
matches these equations and ends with zero live arena bytes. Both packing and
both BLAS clock-count fields were checked for their selected scopes.

Independent audit verified all archive member CRCs/hashes, nine plain retained
copies, 40 archived source hashes against the exact measured Git commit, twelve
exact kernel-returned programs, all raw/native/verification output/cost pairs,
all medians/paired deltas/paired ratios/separate-median ratios and 5,000-resample
paired bootstrap intervals. The runtime's 45-input hash-stability audit passed.
Only the twelve intentional rejecting frontend-capture commands exited nonzero;
all actual acceptance/build/execution/inspection commands passed.

Run the standard-library-only consistency audit:

```sh
python3 experiments/contraction_trees/results/2026-10-31-linux-full/verify.py
```

It verifies preserved evidence using a temporary directory; it does not rebuild
the native program or prove native semantics. Compilation/acceptance times are
retained separately from operation clocks.

## Timing observations and remaining gaps

The table reports medians in microseconds, the median of paired generated/C
ratios, its within-run 95% bootstrap interval, and the distinct ratio of separate
medians. Neither ratio or interval is a controlled-host acceptance test.

| Case / scope | Generated µs | C µs | Paired ratio | 95% interval | Separate medians |
| --- | ---: | ---: | ---: | --- | ---: |
| bulk-complex-p0 / lifecycle | 1483.638 | 1529.696 | 0.9772 | 0.7847–0.9864 | 0.9699 |
| bulk-complex-p0 / reused_buffers | 627.570 | 651.659 | 0.9615 | 0.9533–1.2395 | 0.9630 |
| bulk-complex-p1 / lifecycle | 1537.237 | 1531.136 | 1.0020 | 0.9738–1.0087 | 1.0040 |
| bulk-complex-p1 / reused_buffers | 638.510 | 650.374 | 0.9664 | 0.9436–0.9954 | 0.9818 |
| bulk-f64-p0 / lifecycle | 579.492 | 600.763 | 0.9656 | 0.9625–0.9671 | 0.9646 |
| bulk-f64-p0 / reused_buffers | 185.304 | 210.647 | 0.8911 | 0.8446–0.9360 | 0.8797 |
| bulk-f64-p1 / lifecycle | 590.849 | 611.171 | 0.9538 | 0.9478–0.9791 | 0.9667 |
| bulk-f64-p1 / reused_buffers | 177.313 | 200.962 | 0.8811 | 0.8505–0.9233 | 0.8823 |
| small-complex-p0 / lifecycle | 5.731 | 5.264 | 1.0931 | 1.0692–1.1122 | 1.0888 |
| small-complex-p0 / reused_buffers | 4.132 | 4.173 | 0.9887 | 0.7176–1.0471 | 0.9903 |
| small-complex-p1 / lifecycle | 5.843 | 5.225 | 1.0980 | 1.0499–1.1417 | 1.1183 |
| small-complex-p1 / reused_buffers | 4.234 | 4.213 | 1.0082 | 0.9808–1.0182 | 1.0052 |
| small-f64-p0 / lifecycle | 5.036 | 4.247 | 1.1984 | 1.1804–1.2196 | 1.1858 |
| small-f64-p0 / reused_buffers | 2.138 | 1.852 | 1.1471 | 1.0714–1.2339 | 1.1540 |
| small-f64-p1 / lifecycle | 3.523 | 2.956 | 1.1614 | 0.8346–1.2601 | 1.1916 |
| small-f64-p1 / reused_buffers | 2.283 | 2.034 | 1.0914 | 1.0617–1.1345 | 1.1221 |
| tiny-complex-p0 / lifecycle | 1.596 | 0.921 | 1.6800 | 1.3581–1.7382 | 1.7336 |
| tiny-complex-p0 / reused_buffers | 0.649 | 0.508 | 1.2900 | 1.2481–1.3163 | 1.2758 |
| tiny-complex-p1 / lifecycle | 1.780 | 0.997 | 1.6641 | 1.5101–1.8074 | 1.7858 |
| tiny-complex-p1 / reused_buffers | 0.691 | 0.558 | 1.2688 | 1.1705–1.3415 | 1.2382 |
| tiny-f64-p0 / lifecycle | 1.538 | 0.808 | 1.8286 | 1.7829–1.9487 | 1.9025 |
| tiny-f64-p0 / reused_buffers | 0.937 | 0.402 | 2.1066 | 1.3679–2.3367 | 2.3330 |
| tiny-f64-p1 / lifecycle | 1.581 | 0.878 | 1.8011 | 1.7230–1.9121 | 1.8011 |
| tiny-f64-p1 / reused_buffers | 0.620 | 0.402 | 1.5225 | 1.4637–1.6224 | 1.5424 |

Tiny lifecycle paired overhead is **626–721 ns** (ratios 1.66–1.83); small
lifecycle ratios are 1.09–1.20. Tiny real contiguous reuse has paired ratio 2.1066
and separate-median ratio 2.3330. These costs remain visible; no absolute tiny-call
budget has been accepted.

Bulk lifecycle paired ratios range from 0.9538 to 1.0020 against this original
C loop. Generic regroup diagnostic ratios are unusually favorable (0.196–0.350),
which prompted the stronger block-copy baseline. Even here, bulk complex
contiguous reuse has interval 0.9533–1.2395, crossing the provisional 10% budget.
Differences among scope medians cannot be subtracted to obtain isolated overhead,
and none of these numbers proves an advantage over competent equivalent C.

All 72 final calibration pairs reached the 5 ms target on both sides. Later
measurements still included **79 batches below 5 ms**: 39 lifecycle, 11 reuse and
29 second-BLAS batches; minimum 3,342,254 ns. Every sample was retained. Individual
scope clocks include timer cost, especially significant for tiny kernels.

Arena counters exclude Lean objects, allocator internals and BLAS workspace.
Every recorded process RSS was 147,108 KiB; Linux launcher high-water inheritance
prevents treating this as an isolated executable-heap measurement. Zero timed
arena allocations does not establish zero total allocation or backend packing.

A dedicated controlled host is currently unavailable. Its performance gate is
not waived. The stronger C comparison has its own linked record; runtime/backend
allocation attribution, tiny-call budget, uncertainty and unmeasured profiles
remain open. #69/#183/#222
and historical Stage 1 are not completed by this record.
