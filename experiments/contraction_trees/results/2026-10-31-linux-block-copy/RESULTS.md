# Full Linux tree run against a contiguous-block C baseline

Status: actual generated execution, native validation and paired output/cost
checks passed. **Performance acceptance remains open.** This run uses the
stronger C second-regroup implementation: one `memcpy` for each common contiguous
x block. Within this run, bulk lifecycle and reuse medians are close to C, while
tiny and small operations retain substantial overhead. Uncertainty and the
uncontrolled shared host prevent a performance-gate pass.

The [original coordinate-copy record](../2026-10-31-linux-full/RESULTS.md),
including unfavorable tiny/small measurements, remains intact. The two runs used
different CPU models. Their timing differences are not evidence of a compiler
improvement or a quantified benefit from the comparator change.

## Revision and retained evidence

- [Successful run 41253373151, job 124691336419](https://github.com/MGYamada/Vastitas/actions/runs/41253373151/job/124691336419).
- Measured **clean** commit: `82e00e97a6f93ef0b078bdc086f142c5703c6bc4`.
- Actual harness interval: 2026-10-31 23:40:52–23:45:00 UTC.
- Twelve canonical public check/build/executions, twelve independent kernel
  check/emit executions and twelve wrappers built from the exact emitted resource
  instructions. Twenty-four native builds/executions cover optimized and
  ASan/UBSan/LSan validation for every case.
- **2,650 raw rows = 288 warmup + 778 calibration + 1,584 measurement rows**:
  1,325 generated/C pairs, 72 case/scope groups and eleven measurement pairs per
  group. An additional 288 exhaustive generated/C verification executions ran
  outside timing. Native selftest records are also separate from timings.
- Compact original artifact `13062392347`: **418,711 bytes**, SHA-256
  `330bd49e191354aeca424df38fbb82f32c4f6f4f8331cd22988359657fe16592`.
  [evidence.zip](evidence.zip) retains all 170 members: command logs, public
  packages/wire, returned/generated Lean, wrappers, source snapshots and results.
  [artifact-manifest.json](artifact-manifest.json) records each member's size/hash.
- Large inspection artifact `13062765791`: 60,398,382 bytes, published SHA-256
  `8a41c5b8cbdc910fbf8ceb3900cf1ef1e4de3e47b4492c352b9d002ce596b908`.
  It was **not downloaded or independently content-audited** here. The retained
  command logs record sizes/hashes for its 24 symbol/disassembly files. Twelve
  linked-library listings are in the compact archive. Hosted artifacts use the
  workflow's 14-day retention; the compact archive is retained in this repository.

Plain retained copies are [raw.csv](raw.csv), [summary.json](summary.json),
[summary.md](summary.md), [cases.json](cases.json), [environment.json](environment.json),
[native-validation.json](native-validation.json), [compile-times.json](compile-times.json),
[openblas-build.json](openblas-build.json) and [status.json](status.json).

These measurements precede the later diagonal-metric main commit
`c394716a08f82b7f320c642fd14c5b55a6a3a8e9` and its integration. They are not
measurements of those later production changes or of the final documentation
commit. The exact measured source and binary hashes remain in this record.

## Host and comparison contract

The runner was an **AMD EPYC 9V45 Azure VM**, with four visible logical CPUs.
The harness and child processes were pinned to allowed CPU 0. Frequency, turbo
and unrelated VM/host activity were not controlled. The recorded software was
Linux 7.0.0-1017-azure, glibc 2.43, GCC 15.2.0, Rust 1.99.1 and pinned Lean 4.35.0.
Load averages changed from `3.93 1.68 0.64` to `1.53 1.59 0.85`. The earlier
coordinate-copy run used EPYC 9V74; this is not a paired experiment across runs.

Both implementations use the same static sequential LP64 OpenBLAS 0.3.34
HASWELL archive, SHA-256
`1ca3e930bb5e5ec46000ea7978e019abb3076d31eb56bc382b030ac46051fcaa`,
one thread and `NativeFast`. The frontend was built in release mode; generated
native code and C use `-O3 -fno-lto`. Neither fast-math nor an alternate BLAS
backend is introduced by this comparison.

Each repetition preserves **pack → first GEMM → regroup → second GEMM**, with
the same coefficients, scalar types, logical dimensions, physical layouts and
padding. The C comparison calls direct CBLAS and performs its own first pack and
second regroup, with descriptor/scalar/shape/disjoint-allocation/counter checks
before writes. Both packs copy contiguous x blocks. For the second regroup,
source element `x+i*y+ld_input*a` maps to `x+i*a+ld_output*y`; grouping the x cells
into one `i*w`-byte copy preserves their exact byte mapping, copied bytes and
padding. This strengthens only the experiment's comparator; no production
compiler/runtime optimization was made for this run.

The finite cases are `(i,k,j,a,b)` = tiny `(2,3,4,5,6)`, small `(7,17,5,11,13)`
and bulk `(24,40,32,48,56)`, each real/complex and contiguous/padded. There are six
caller allocations: T, A, B, scratch, middle and C. Scratch is explicitly reused.
The C and generated paths share arena allocation/setup primitives; this does not
compare alternative allocators. At most 2,825,248 arena data bytes are live.
Fresh initialization followed by reuse is not a cold-cache/DRAM workload.

## Exact costs and independent audit

Let `w` be 8 or 16, `P=w*i*k*j`, `R=w*i*j*a`, and `C=w*i*a*b`.
Each four-operation repetition writes `P+2R+C` bytes and copies `P+R` bytes.
Lifecycle performs six data allocations/frees per repetition; the reused timed
window performs none. Scratch capacity is the maximum of its two explicit
packing footprints, including physical padding/offsets. Lifecycle initialization
additionally writes all six capacities plus `w*(i*k*j+k*a+j*b+6)` bytes.

All raw, native-selftest and separate verification rows match these equations
and finish with zero live arena data bytes. Each arena has two metadata
allocations and 280 peak metadata bytes in this recorded x86-64 ABI: an 88-byte
arena and eight 24-byte buffer entries. Reused timed windows allocate no arena
metadata. Packing/BLAS clock-count fields match their selected diagnostic scopes.

Independent audit checked every archive CRC/member hash, all nine plain copies,
all 40 archived source files against the exact measured Git commit, all 2,650
raw rows against command stdout, all native/verification output and cost pairs,
and all twelve emit responses/canonical results/generated-wrapper instruction
sequences. The run's 45-input stability guard passed. Medians, quartiles,
extrema, MAD, paired deltas/ratios, separate-median ratios and 5,000-resample
paired bootstrap intervals were independently recomputed. Only twelve
intentional rejecting frontend-capture commands exited nonzero; actual
acceptance/build/execution/inspection commands passed.

Reproduce the consistency audit with Python's standard library and Git, with
the measured commit available locally:

```sh
python3 experiments/contraction_trees/results/2026-10-31-linux-block-copy/verify.py
```

The audit writes no project files, rebuilds nothing and proves no native
semantics. Compilation/acceptance time is retained separately from operation
clocks. Timed lifecycle rows use lightweight output checks; exhaustive buffer,
padding and mutation checks are separate verification/selftest executions.

## Lifecycle and reuse observations

Times are medians in microseconds. The paired ratio is the median of the eleven
generated/C sample ratios; the interval is a within-run paired bootstrap interval.
The last column is the distinct ratio of the two separate medians. Neither is a
controlled-host acceptance test. Ratios above 1 mean generated execution took
longer than this block-copy C implementation in the indicated scope.

| Case / scope | Generated µs | C µs | Paired ratio | 95% interval | Separate medians |
| --- | ---: | ---: | ---: | --- | ---: |
| bulk-complex-p0 / lifecycle | 1426.461 | 1294.646 | 1.0320 | 0.9913–1.1282 | 1.1018 |
| bulk-complex-p0 / reused_buffers | 506.884 | 507.682 | 0.9987 | 0.9632–1.0195 | 0.9984 |
| bulk-complex-p1 / lifecycle | 1302.438 | 1349.156 | 0.9879 | 0.9561–1.0043 | 0.9654 |
| bulk-complex-p1 / reused_buffers | 509.279 | 512.311 | 0.9959 | 0.9487–1.0239 | 0.9941 |
| bulk-f64-p0 / lifecycle | 520.199 | 573.387 | 1.0014 | 0.9425–1.0459 | 0.9072 |
| bulk-f64-p0 / reused_buffers | 142.660 | 139.089 | 1.0147 | 1.0006–1.0362 | 1.0257 |
| bulk-f64-p1 / lifecycle | 496.358 | 484.144 | 1.0180 | 0.9785–1.0664 | 1.0252 |
| bulk-f64-p1 / reused_buffers | 137.007 | 137.262 | 0.9981 | 0.9232–1.0539 | 0.9981 |
| small-complex-p0 / lifecycle | 4.391 | 3.654 | 1.2651 | 1.0395–1.2796 | 1.2019 |
| small-complex-p0 / reused_buffers | 3.125 | 2.624 | 1.1109 | 1.0708–1.3958 | 1.1905 |
| small-complex-p1 / lifecycle | 4.383 | 3.491 | 1.2584 | 1.2261–1.4481 | 1.2555 |
| small-complex-p1 / reused_buffers | 2.999 | 2.870 | 1.0776 | 1.0520–1.1178 | 1.0449 |
| small-f64-p0 / lifecycle | 2.896 | 1.900 | 1.5559 | 1.4245–1.6080 | 1.5243 |
| small-f64-p0 / reused_buffers | 1.542 | 1.178 | 1.3397 | 1.2562–1.6538 | 1.3094 |
| small-f64-p1 / lifecycle | 3.451 | 2.137 | 1.4299 | 1.3661–1.5703 | 1.6148 |
| small-f64-p1 / reused_buffers | 1.600 | 1.310 | 1.1878 | 1.1692–1.2519 | 1.2213 |
| tiny-complex-p0 / lifecycle | 1.501 | 0.714 | 2.0881 | 1.6580–2.1152 | 2.1029 |
| tiny-complex-p0 / reused_buffers | 0.511 | 0.374 | 1.4095 | 1.2571–1.4714 | 1.3671 |
| tiny-complex-p1 / lifecycle | 1.679 | 0.823 | 2.1016 | 1.8382–2.1986 | 2.0387 |
| tiny-complex-p1 / reused_buffers | 0.747 | 0.494 | 1.4028 | 1.3630–1.4510 | 1.5107 |
| tiny-f64-p0 / lifecycle | 1.619 | 0.646 | 2.2248 | 2.1461–2.3344 | 2.5088 |
| tiny-f64-p0 / reused_buffers | 0.492 | 0.347 | 1.4834 | 1.2676–1.8366 | 1.4177 |
| tiny-f64-p1 / lifecycle | 1.520 | 0.763 | 2.0860 | 1.8276–2.1513 | 1.9918 |
| tiny-f64-p1 / reused_buffers | 0.472 | 0.316 | 1.4865 | 1.4519–1.5104 | 1.4916 |

Tiny lifecycle paired ratios are **2.0860–2.2248**, with paired overhead
**770–853 ns**; reuse ratios are **1.4028–1.4865**, or **153–213 ns** overhead.
Small lifecycle ratios are **1.2584–1.5559**, with **888–1,089 ns** overhead;
small reuse is **1.0776–1.3397**, or **255–396 ns** overhead. No absolute tiny-call
budget has been accepted, and these unfavorable results remain part of the record.

Bulk lifecycle paired ratios are **0.9879–1.0320**, while reuse is
**0.9959–1.0147**. Bulk complex contiguous lifecycle still has interval
**0.9913–1.1282**, crossing the provisional 10% budget; its separate-median ratio
is 1.1018. Bulk real contiguous lifecycle illustrates why the two statistics must
not be conflated: paired ratio 1.0014 versus separate-median ratio 0.9072. This
record does not establish a generated-code speedup, parity or cross-host stability.

## Diagnostic scopes and remaining limits

Diagnostic ratios below are ranges across the four scalar/layout cases within
each size. They time a selected packing/preflight or CBLAS call while executing
the full schedule; they exclude FFI. Timers and context affect tiny measurements.

| Size | First pack | Second regroup | First BLAS | Second BLAS |
| --- | ---: | ---: | ---: | ---: |
| tiny | 1.2711–1.3684 | 1.5328–1.6016 | 0.9569–1.0868 | 0.9975–1.0587 |
| small | 0.9949–1.9277 | 1.5987–2.0745 | 0.9852–1.0510 | 0.9544–1.1427 |
| bulk | 1.0390–1.1271 | 1.0017–1.0531 | 0.9912–1.0331 | 1.0030–1.0150 |

Second-regroup paired overhead is **20–23 ns** for tiny, **53–105 ns** for small,
and **8–489 ns** for bulk. Small real contiguous first-pack ratio is 1.9277
(interval 1.8338–2.0207), and small real padded first-pack ratio is 1.8240
(1.7871–1.8493). Bulk real first-pack ratios are 1.1148–1.1271, with interval
upper bounds above 1.12. Small real contiguous second BLAS also records 1.1427
(1.1024–1.1970). The same BLAS backend is used, but such diagnostic differences
are observations rather than attribution to a particular overhead source.
Differences between scope medians cannot be subtracted to isolate FFI/checking cost.

All **72 final calibration pairs** reached 5 ms on both sides; the minimum final
calibration batch was 5,004,732 ns. Later measurements retained **88 batches below
5 ms**: 19 reuse, 22 second-BLAS, 25 first-BLAS, 15 first-pack and 7 lifecycle;
the minimum was 3,685,492 ns. No samples were discarded or selectively recalibrated.

Every recorded timed process RSS was **146,880 KiB**. Linux launcher high-water
inheritance prevents treating that value as an isolated executable-heap
measurement. Arena counters exclude Lean objects, allocator internals and BLAS
private workspace/packing. Zero timed arena allocations does not establish zero
total allocation. The large symbol/disassembly artifact was not independently
inspected, so this audit makes no additional instruction-level attribution.

A dedicated controlled host is currently unavailable; its gate is **not waived**.
Remaining work includes controlled repeatability/uncertainty, tiny-call budgets,
runtime/backend allocation attribution and unmeasured rank/layout/tree profiles.
The bounded block-copy comparison improves the evidence available for those
decisions; it does not complete #69/#183/#222 or historical Stage 1.
