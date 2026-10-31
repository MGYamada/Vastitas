# 2026-10-31: full public GEMM measurement on a hosted runner

All 24 public cases passed independent checking, canonical generated execution,
native sanitizers and matched output/cost validation. This is an exploratory
measurement on one shared host, **not performance acceptance or C parity**.
Tiny calls retain measurable overhead; bulk results vary by sample and statistic.
The controlled-host, total-memory and declared tiny-budget obligations in
[#222](https://github.com/MGYamada/Vastitas/issues/222) remain open.

## Exact revision and host

- Measured clean commit: `38b96ae5a6b0610ec71babf199e7635867cca023`,
  before later main integrations. These numbers are not measurements of those
  later compiler revisions.
- [Manual full job](https://github.com/MGYamada/Vastitas/actions/runs/41198941654/job/124530710574).
  The harness ran from 12:00:10 to 12:05:24 UTC on 2026-10-31.
- AMD EPYC 7763, four visible logical CPUs, Microsoft virtualization; affinity
  pinned to CPU 0. Linux 7.0.0-1017-azure, glibc 2.43, GCC 15.2.0,
  Lean 4.35.0 and Rust 1.99.1. Recorded load averages were
  `4.61 2.40 0.97` before and `2.14 2.12 1.25` after the run.
- Explicit `NativeFast`, `-O3`, `-fno-lto`, no fast-math. Both paths used the
  same sequential LP64 OpenBLAS 0.3.34 HASWELL archive, SHA-256
  `1ca3e930bb5e5ec46000ea7978e019abb3076d31eb56bc382b030ac46051fcaa`.
  Backend and thread checks reported one thread.

```sh
python3 experiments/public_gemm/run.py \
  --prefix "$RUNNER_TEMP/gemm-openblas" \
  --output "$RUNNER_TEMP/public-gemm-results" \
  --samples 11 --target-ms 5
```

No `--smoke`, `--allow-unavailable` or `--no-leak-sanitizer` was used.
The [method](../../README.md) defines the matched-work C baseline, warmup,
initialization, accumulating recurrence, oracle and scope boundaries. The C side
uses the same arena and directly calls CBLAS; it is not a comparison against
arbitrary best C implementations or a different algorithm/backend.

## Validation and observable costs

| Check | Result |
| --- | --- |
| Public source cases | 24: real/complex × contiguous/padded × overwrite/accumulate × tiny/small/bulk |
| Independent kernel `check` and `emit` | 24 of each passed |
| Normal CLI `check`, `build`, unmodified executable | 24 of each passed; each executable printed `0` |
| Emitted measurement wrappers | 24 compiled and executed |
| Native correctness and ASan/UBSan/LSan | 24 optimized plus 24 sanitized records passed |
| Separate exhaustive runtime validation | 288 process invocations passed |
| Raw rows | 2,512: 288 warmup, 640 calibration, 1,584 measurement |
| Complete generated/C pairs | 1,256, including 792 measurement pairs |
| Measurement groups | 72, each with 11 alternating equal-repetition pairs |

Every paired checksum and arena cost matched. All cleanup left zero live matrix
bytes and equal data allocations/frees. Lifecycle uses three data allocations
per operation; prepared scopes allocate and copy zero matrix bytes inside their
window. Peak matrix capacity is 208–4,893,936 bytes, including padding. Initialization
and GEMM writes remain recorded separately from copies. Counter equality does
not count Lean objects, allocator overhead or BLAS-private packing/workspace.

The 24 nonzero frontend-capture exits are intentional `E_CAPTURED` responses,
which only retain requests for the subsequent real independent checker. They
are not acceptance. No other command failed. The pinned BLAS archive itself is
not sanitizer-instrumented.

The 5 ms value is a calibration target: 142 of the 1,584 measurement batches
subsequently fell below it (66 lifecycle, 18 prepared-call, 58 BLAS-kernel).
The minimum was 2.995689 ms. Every final calibration pair reached the target
in 1–7 attempts, without reaching the repetition cap. Bulk complex cases used
one operation per batch; bulk real cases used 2–4 depending on scope. Tiny
lifecycle batches used 6,465–12,208 operations. No sample was discarded or
silently replaced.

## Bulk results

Bulk dimensions are `(M,N,K) = (384,320,256)`. Values below are per operation;
all 11 paired samples contribute. `p0` is contiguous and `p1` padded.
`Pair ratio` is **median(generated[i] / C[i])**; `Median ratio` is the distinct
**median(generated) / median(C)**. The interval is the paired 5,000-resample
percentile interval for this run only; it excludes uncertainty across hosts/runs.
The two ratios need not agree and neither is selectively used as a pass.

### Full resource lifecycle

| Case | Generated median (ms) | C median (ms) | Pair ratio | Pair 95% interval | Median ratio |
| --- | ---: | ---: | ---: | --- | ---: |
| complex-p0-accumulate | 9.5656 | 9.8369 | 1.0054 | 0.9727–1.0360 | 0.9724 |
| complex-p0-overwrite | 7.7330 | 7.7822 | 0.9968 | 0.9935–1.0021 | 0.9937 |
| complex-p1-accumulate | 8.5169 | 8.1571 | 1.0315 | 0.9777–1.0844 | 1.0441 |
| complex-p1-overwrite | 8.0124 | 8.5035 | 0.8983 | 0.8343–1.0494 | 0.9423 |
| f64-p0-accumulate | 2.5783 | 2.5109 | 1.0116 | 1.0074–1.2522 | 1.0268 |
| f64-p0-overwrite | 2.4648 | 2.4550 | 1.0065 | 0.9915–1.0156 | 1.0040 |
| f64-p1-accumulate | 2.6283 | 2.6172 | 1.0206 | 0.9489–1.1078 | 1.0043 |
| f64-p1-overwrite | 3.1040 | 2.5693 | 0.9977 | 0.9893–1.0057 | 1.2081 |

### Repeated prepared call

| Case | Generated median (ms) | C median (ms) | Pair ratio | Pair 95% interval | Median ratio |
| --- | ---: | ---: | ---: | --- | ---: |
| complex-p0-accumulate | 5.9094 | 5.9659 | 0.9917 | 0.9335–1.0405 | 0.9905 |
| complex-p0-overwrite | 5.3855 | 5.4369 | 0.9918 | 0.9760–1.0046 | 0.9905 |
| complex-p1-accumulate | 5.8298 | 5.8691 | 1.0108 | 0.8592–1.0669 | 0.9933 |
| complex-p1-overwrite | 5.7252 | 5.3895 | 1.0427 | 0.9710–1.0795 | 1.0623 |
| f64-p0-accumulate | 1.4714 | 1.7413 | 0.9909 | 0.8418–1.0483 | 0.8450 |
| f64-p0-overwrite | 1.4583 | 1.4516 | 1.0125 | 0.9316–1.0316 | 1.0047 |
| f64-p1-accumulate | 1.4983 | 1.5202 | 0.9735 | 0.9135–1.0404 | 0.9856 |
| f64-p1-overwrite | 1.4042 | 1.3896 | 1.0030 | 0.9941–1.0150 | 1.0105 |

Lifecycle includes arena setup, allocation, initialization, preflight, GEMM,
observation, cleanup and accounting. Prepared-call excludes setup/cleanup but
includes the generated Lean loop, FFI, preflight and write accounting.
The BLAS-only diagnostic is preserved in [all summaries](summary.md); it cannot
establish public-path overhead or be subtracted from scope medians.

For example, padded real overwrite has lifecycle pair ratio 0.9977 but ratio
of separate medians 1.2081. The contiguous/padded real accumulate lifecycle
intervals reach 1.2522/1.1078. These differing observations and shared-host
variation prevent a controlled 10% performance acceptance claim. The bulk
matrices occupy under 5 MB, and fresh initialization/reuse does not test
cold-cache or DRAM-scale behavior.

## Tiny and small calls

The tiny dimensions are `(2,3,4)`. Report absolute paired differences as well as
ratios because fixed call costs are significant at this size.

| Tiny case | Lifecycle paired difference (ns) | Lifecycle pair ratio | Prepared paired difference (ns) | Prepared pair ratio |
| --- | ---: | ---: | ---: | ---: |
| complex-p0-accumulate | 359.5 | 1.6524 | 82.8 | 1.3520 |
| complex-p0-overwrite | 354.8 | 1.6852 | 61.8 | 1.2841 |
| complex-p1-accumulate | 400.1 | 1.6414 | 127.7 | 1.3463 |
| complex-p1-overwrite | 343.8 | 1.6692 | 72.3 | 1.3250 |
| f64-p0-accumulate | 390.3 | 1.6114 | 65.3 | 1.2924 |
| f64-p0-overwrite | 331.0 | 1.6338 | 72.4 | 1.3509 |
| f64-p1-accumulate | 399.2 | 1.7039 | 84.7 | 1.3652 |
| f64-p1-overwrite | 329.4 | 1.6737 | 66.9 | 1.3036 |

For tiny contiguous complex overwrite in the prepared scope, the paired
difference is +61.8 ns and pair ratio 1.2841, while the separate medians are
256.75 ns generated and 370.77 ns C (median ratio 0.6925). The samples move
between timing clusters, so the separate medians can invert the paired result.
Both observations are retained; this is another reason not to infer acceptance
from a selected statistic.

Tiny lifecycle is 329–400 ns slower per operation (pair ratios 1.61–1.70).
Prepared calls retain 62–128 ns (1.28–1.37). Small `(17,13,19)` cases have
lifecycle pair ratios 1.19–1.31 and prepared ratios 1.08–1.14. These are observed
remaining gaps, not an accepted tiny-call budget or attribution to one runtime
component. A tiny absolute budget must be set before accepting this gate;
this run does not choose a threshold after seeing the measurements.

## Durable evidence and remaining scope

[Raw rows](raw.csv), [all summaries](summary.json), [environment](environment.json),
[cases](cases.json), [compile records](compile-times.json),
[native/sanitizer records](native-validation.json) and [backend build](openblas-build.json)
are copied byte-for-byte from the successful artifact. Compile/check wall times
are separate from runtime; they include process startup and existing build-cache
state and do not form a standalone compile-latency experiment.

The [source and command archive](source-and-commands.tar.gz) preserves every
source package/wire request, independent checker response, exact emitted source,
wrapper, recorded runtime source and command log. It is 183,666 bytes, SHA-256
`4b2d144fb238ac31c0aca85fd53ef64f4846d85aea4eb68d336ab65a7b11b45f`.
The [manifest](artifact-manifest.json) records hashes/sizes of all 325 original
artifact members and where each is retained. Large disassemblies/symbol listings
remain in the original temporary artifact; their hashes are recorded here.
No binary or full disassembly is committed.

The [original artifact](https://github.com/MGYamada/Vastitas/actions/runs/41198941654/artifacts/13041259847)
is 120,455,882 bytes, SHA-256
`cf4c3ec94207f988637668ecac3f8a58560b8d882995a649506795be549d0865`,
with hosted retention through 2026-11-14. Its complete hash and all ZIP CRCs were
verified before analysis. The durable files above do not depend on that retention.

`ru_maxrss` ranged from 62,572 to 74,148 KiB. It can include the launcher's pre-exec
footprint and is not an isolated generated-executable/Lean/BLAS heap measurement.
BLAS-private packing/allocation counts, total process allocation counts, independent
host/run uncertainty, explicit tensor packing/retention, dynamic dimensions,
other transpose/adjoint profiles and a declared tiny-call budget remain outside
this run. #222/#92/#183/#179 stay open; this record does not prove native
refinement or complete historical Stage 1.
