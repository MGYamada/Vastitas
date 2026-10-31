# 2026-10-31: full Linux tensor packing measurement

All twelve cases passed actual public checking, canonical generation/execution,
matched C output/cost checks and native ASan/UBSan/LSan. This is an exploratory
shared-host measurement, **not C parity or controlled performance acceptance**.
Tiny/small overhead and uncertain bulk results remain visible in the retained
raw samples. The workload packs on every repeated operation; it does not measure
cached packing, general regrouping or multi-edge contraction trees.

## Revision, host and command

- Measured clean commit: `3c1664c698be93041012b5768a76f4fc0d975b31`,
  before the later cached-packing main integration. Later compiler revisions
  are not assigned these measurements.
- [Successful full job](https://github.com/MGYamada/Vastitas/actions/runs/41210231176/job/124563505139).
  Harness interval: 2026-10-31 14:31:15–14:34:12 UTC.
- AMD EPYC 7763, four visible logical CPUs, Microsoft virtualization,
  CPU 0 affinity; Linux 7.0.0-1017-azure/glibc 2.43, GCC 15.2.0,
  Lean 4.35.0, Rust 1.99.1. Load averages changed from
  `4.36 2.24 0.90` to `2.30 2.17 1.10`.
- Explicit NativeFast, `-O3`, no LTO/fast-math; the same sequential LP64
  OpenBLAS 0.3.34 HASWELL archive on both sides, one thread, SHA-256
  `1ca3e930bb5e5ec46000ea7978e019abb3076d31eb56bc382b030ac46051fcaa`.

```sh
python3 experiments/tensor_packing/run.py \
  --prefix "$RUNNER_TEMP/tensor-openblas" \
  --output "$RUNNER_TEMP/tensor-packing-results" \
  --samples 11 --target-ms 5
```

No smoke or sanitizer fallback was used. The [method](../../README.md) describes
all scope, reuse-wrapper and finite-oracle boundaries. Both sides use the same
arena setup and explicit scratch. The C baseline has an independent block-copy
packing loop and direct CBLAS call; it does not call the production packing or
GEMM adapter. This is matched work, not comparison with every possible optimized
C algorithm. The native sanitizer checks do not instrument the complete Lean
executable or prebuilt BLAS archive.

## Independently rechecked evidence

| Check | Result |
| --- | --- |
| Source cases | 12: real/complex × contiguous/padded × three sizes |
| Independent kernel check/emit | 12 of each passed; emitted source equals the saved response |
| Canonical CLI check/build/executable | 12 of each passed; executables print `0` |
| Generated measurement wrappers | All 12 compiled and executed |
| Native records | 12 optimized plus 12 ASan/UBSan/LSan passed |
| Separate exhaustive runtime validation | 192 process invocations / 96 pairs passed |
| Raw rows | 1,754: 192 warmup, 506 calibration, 1,056 measurement |
| Complete generated/C pairs | 877, including 528 measurement pairs |
| Measurement groups | 48, each with 11 alternating equal-repetition pairs |
| Source record hashes | All 30 archived source hashes matched |

All paired outputs/checksums and arena costs match. The audit independently
recomputes physical capacities, initialization, packing/output writes, allocations,
frees and timed counters from each case's dimensions and padding. It also
recomputes medians, paired differences, both ratio statistics and 5,000-resample
paired intervals. Twelve nonzero `E_CAPTURED` exits deliberately retain frontend
wire requests; subsequent actual checks perform acceptance. No other command
failed.

Let `w` be 8/16 bytes, `P=i*k*j*w`, `O=i*j*l*w` and `S` the total capacity of
four caller buffers. Each operation copies `P` bytes and writes `P+O` bytes
after initialization. Lifecycle has four allocations/frees per repetition;
reused-buffer scopes have zero timed data allocations/frees but still copy `P`
bytes each repetition. Peak data is `S`, 824–1,747,296 bytes in this run; final
live bytes are zero. All four logical buffers and padding have untimed full
oracles, including a wrong-flat-copy mutation that must reject both packed
coordinates and the resulting output. These counters omit Lean/allocator and
BLAS-private memory.

Eighty measurement batches fell below the 5 ms calibration target: 14 lifecycle,
24 reused-buffer, 31 pack-adapter and 11 BLAS-kernel. The shortest was 3.179463 ms.
All samples remain in the record; the target is not a post hoc exclusion rule.

## Bulk measurements

Bulk axes `(i,k,j,l) = (32,48,24,40)`; `p0` is contiguous and `p1` padded.
`Pair ratio` means median of the eleven generated/C ratios. `Median ratio`
means ratio of the two separate medians. The paired percentile interval covers
within-run resampling only, not independent host/run uncertainty.

### Full lifecycle

| Case | Generated median (ms) | C median (ms) | Pair ratio | Pair 95% interval | Median ratio |
| --- | ---: | ---: | ---: | --- | ---: |
| complex-p0 | 1.3272 | 1.3330 | 0.9993 | 0.7954–1.0139 | 0.9957 |
| complex-p1 | 1.1491 | 1.0882 | 1.0487 | 1.0066–1.0662 | 1.0559 |
| f64-p0 | 0.5610 | 0.5561 | 1.0082 | 0.9956–1.0988 | 1.0088 |
| f64-p1 | 0.4483 | 0.4480 | 1.0017 | 0.9746–1.0200 | 1.0006 |

### Reused buffers, packing every operation

| Case | Generated median (ms) | C median (ms) | Pair ratio | Pair 95% interval | Median ratio |
| --- | ---: | ---: | ---: | --- | ---: |
| complex-p0 | 0.4090 | 0.3445 | 1.0024 | 0.9106–1.2179 | 1.1874 |
| complex-p1 | 0.3247 | 0.3247 | 1.0069 | 0.9778–1.1478 | 1.0001 |
| f64-p0 | 0.0988 | 0.0986 | 1.0020 | 0.9966–1.0144 | 1.0027 |
| f64-p1 | 0.1005 | 0.1209 | 0.9913 | 0.7819–1.0173 | 0.8310 |

The bulk complex reused-buffer intervals reach 1.1478/1.2179, crossing the
provisional 10% budget. Contiguous complex reused buffers have pair ratio 1.0024
but separate-median ratio 1.1874. No statistic is selected to convert uncertainty
into a pass. These buffers fit under 1.75 MB and the experiment does not measure
cold-cache/DRAM-scale traffic. Pack-only and BLAS-only diagnostics remain in
[all summaries](summary.md); they are not public-path performance and their
medians must not be subtracted to invent isolated overhead.

## Tiny and small overhead

Tiny axes are `(2,3,4,5)` and small axes `(7,11,5,13)`. Fixed call costs are
reported as absolute paired differences as well as ratios.

| Case | Lifecycle difference (ns) | Lifecycle pair ratio | Reused difference (ns) | Reused pair ratio |
| --- | ---: | ---: | ---: | ---: |
| small-complex-p0 | 653.8 | 1.2085 | 188.2 | 1.1027 |
| small-complex-p1 | 546.5 | 1.1895 | 298.9 | 1.1345 |
| small-f64-p0 | 628.7 | 1.3534 | 181.7 | 1.1919 |
| small-f64-p1 | 690.0 | 1.4344 | 206.8 | 1.2179 |
| tiny-complex-p0 | 721.3 | 1.6034 | 135.8 | 1.3665 |
| tiny-complex-p1 | 436.3 | 1.5993 | 146.8 | 1.2798 |
| tiny-f64-p0 | 570.8 | 1.6986 | 148.3 | 1.6332 |
| tiny-f64-p1 | 408.3 | 1.6536 | 110.7 | 1.4529 |

Tiny lifecycle retains 408–721 ns overhead; small lifecycle pair ratios are
1.19–1.43. Reusing buffers still retains both packing and FFI/adapter costs.
A tiny absolute acceptance budget has not been predeclared; this run does not
set one after observing the results. Host variation can also invert separate
medians: tiny padded complex reused buffers have pair ratio 1.2798 while the
separate-median ratio is 0.9454. Both statistics and every sample are preserved.

## Durable artifact and limits

The complete [compact evidence ZIP](evidence.zip) is a byte-for-byte copy of
[artifact 13045813725](https://github.com/MGYamada/Vastitas/actions/runs/41210231176/artifacts/13045813725):
296,099 bytes, SHA-256
`f4d07e4da544246a470c23ab626ea13dba38daaa07f3e445b444cee76329e55d`.
Its hash and all 160 ZIP member CRCs were verified. The
[manifest](artifact-manifest.json) supplies every member's byte count and hash.
The ZIP includes raw data, commands, compiler/check records, native/sanitizer
records, exact source packages/wire/emission/wrappers, runtime sources and
linked-library inspection. Selected records are also available directly:
[raw rows](raw.csv), [summary](summary.json), [environment](environment.json),
[cases](cases.json), [compile records](compile-times.json) and
[native validation](native-validation.json).

Recheck the preserved hashes, source/emission records, paired costs and statistics
without rebuilding native programs:

```sh
python3 experiments/tensor_packing/results/2026-10-31-linux-full/verify.py
```

Large disassembly/symbol files are separate
[artifact 13045399358](https://github.com/MGYamada/Vastitas/actions/runs/41210231176/artifacts/13045399358),
60,137,808 bytes, published digest
`a6a70339df07ad1ab5f42358be55e546762233c1794104a73467a8cd6d66ad75`.
They were not downloaded for this compact-data audit; their recorded per-file
hashes remain in the command log. Hosted artifacts expire on 2026-11-14, while
the committed compact ZIP remains durable. Compile/check wall times remain
separate from runtime and include startup/cache state.

Every recorded RSS sample is 146,512 KiB. This can retain the launcher's pre-exec
footprint and does not isolate generated-process heap or BLAS-private packing.
Total allocations/backend memory, controlled-host repeats, larger working sets,
predeclared tiny budgets, cached packing, generic regrouping and multi-edge
execution performance remain separate obligations. This record does not prove
native refinement or complete #69/#183/#222/#179 or historical Stage 1.
