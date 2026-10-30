# Optional synchronous C storage-copy baseline

This experiment compares the actual `vstorage_copy` C adapter with a conventional
C copy of the same logical matrix. It is **not** a measurement of Vastitas source
execution, Lean FFI, the protocol-8 pipeline, GEMM, GPU execution, or native
refinement. It adds no production API, profiler, CI job, package gate, performance
threshold, or completion claim for [#183](https://github.com/MGYamada/Vastitas/issues/183)
or [#222](https://github.com/MGYamada/Vastitas/issues/222).

Recorded runs: [latest post-#280 results](results/2026-10-30-epyc-post280/RESULTS.md)
and [earlier pre-#280 results](results/2026-10-30-epyc/RESULTS.md).

## Reproduce

From the repository root, with Python 3 and a C11 compiler on a 64-bit POSIX host:

```sh
python3 experiments/storage_copy/run.py --output /tmp/storage-copy-run
```

The output directory must not exist. `--cc gcc`, `--cpu 0`, `--samples 21`, and
`--target-ms 10` select the compiler, allowed Linux CPU, paired sample count and
calibration target. Defaults: `CC` or `cc`, first allowed CPU on Linux, 11 pairs,
at least 5 ms for both implementations when calibration permits. The binary is
single-threaded. The harness does not change frequency, turbo, system load, or
allocator settings. Run on an otherwise idle controlled host for stronger evidence.

`--smoke --samples 3 --target-ms 0.1` checks all layout combinations at small sizes;
it is not a performance result. ASan/UBSan run separately before timing; an
unsupported sanitizer is a failure, not a silent skip. If LeakSanitizer cannot
inspect processes in a restricted container, use `--no-leak-sanitizer` and report
that limitation. `--skip-sanitizers` records an explicit omission.

## Comparison contract

The C baseline deliberately uses **the same** arena allocator, exact `prepare`
function, handle/representation/shape/bounds/alignment/narrowing/alias checks,
overflow checks, counters, and cleanup. Its boundary mirrors `vstorage_copy`;
contract tests check failure-before-write, missing/closed handles, mismatched
representations and shapes, alias rejection, disjoint same-allocation copying,
counter overflow, exact self-copy and allocation-budget cleanup. This controls
safety work rather than comparing an unchecked C loop against a checked API.
It does **not** independently validate the shared safety implementation or measure
the cost of the arena against an alternative C ownership design.

The baseline element loop is separately written using column base pointers and
row strides; it never calls the adapter's copy loop. Both use the same logical
column-then-row order, binary64/interleaved two-binary64 complex representation,
nonconjugating transpose, single-pass algorithm, `restrict` only after validated
disjoint envelopes, compiler and flags. Neither is a tiled transpose, packing
routine, hand-tuned memcpy benchmark, or claim of the fastest achievable C copy.

`probe.c` includes the unmodified production `storage.c` in an **experiment-only**
translation unit to inspect fixtures and call the private kernel. The driver is a
separate translation unit; `-fno-lto` is used at compile and link time. Full/checked
measurements call the actual public `vstorage_copy` symbol. The optional native
package and its API remain unchanged. Private prepared references do not escape
the experiment or authorize unchecked production calls.

| Scope | Timed work | Work outside timing |
|---|---|---|
| `lifecycle` (primary) | Arena creation, data allocation, checked full-buffer fixture initialization, both copy preflights, copy/early return, accounting, constant-size output observation, close/drop, stats capture, metadata cleanup, driver aggregation | Exhaustive verification of this path before and after measurement; warmup and calibration |
| `checked_call` | Repeated public copy call including both preflights, alias/overflow checks, early return or loop, counters and status check | Allocation, initialization, exhaustive output verification and cleanup; zero timed allocations on both sides |
| `loop_only` (reference) | Out-of-line prepared element loop and call overhead | Allocation, initialization, boundary validation, preparation, accounting, verification and cleanup |

Lifecycle initialization is a common benchmark fixture, not a generated Vastitas
program: a checked full-allocation view is populated with deterministic bit
patterns (source) or a quiet-NaN sentinel (destination). Its cost is included on
both sides. Direct fixture writes are reported separately as `fixture_written_bytes`;
they are not misreported as runtime `written_bytes`. This initialization can
dominate lifecycle time, so checked-call results must be considered alongside it.
The lifecycle's O(1) observation and stats aggregation are common harness costs,
and are not subtracted. No Lean object allocation or FFI overhead is included.

The prepared-loop wrapper has a different compiler specialization context from
the inlined kernel inside a checked copy. Timing variation and that context can
make a prepared-loop sample slower than a checked call. Do not subtract the two
measurements to estimate preflight cost; they are separately measured scopes.

## Cases and correctness

There are 160 real-copy cases: 2 scalar kinds × 4 independent source/destination
padding combinations × 4 transpose combinations × 5 sizes. Logical dimensions are
0×7, 2×3, 16×17, 128×129 and 2048×2051. Rectangles expose swapped-index errors.
Physical dimensions swap under transpose to keep logical input/output shapes
equal. Padded source uses a 2-element prefix, +3 leading dimension and 3-element
suffix; padded destination uses a 3-element prefix, +5 leading dimension and
3-element suffix. Unpadded views are contiguous and empty unpadded allocations
have no data allocation. The bulk source+destination working set is approximately
64 MiB for real and 128 MiB for complex, larger than the recorded host's 32 MiB L3;
this is not a claim of guaranteed cold-cache or DRAM-only traffic.

Another 40 cases are exact same-allocation, same-view self-copy, with independent
size/scalar/padding/transpose coverage. They use one allocation, perform both
preflights, and move **zero** bytes. Empty and self-copy cases have no `loop_only`
results and no copy-bandwidth interpretation. Self-copy is never pooled with
real-copy timings.

The correctness oracle inspects every source and destination word bit-for-bit,
including leading/inter-column/trailing padding, after every checked/loop batch.
It derives logical coordinates by inverting destination physical coordinates and
maps them to source physical coordinates, independently of both loops. The source
contains +0, -0, infinities, quiet/signaling NaN payloads and index-dependent finite
bits; complex components are independently patterned. No FP arithmetic or
implicit conjugation is allowed. Deliberate source/output/padding corruptions
must be detected. Lifecycle executions get exhaustive checks before and after
timing, plus constant-size observation on every timed iteration. Outputs and
cost counters must match across each pair.

Opaque external calls without LTO prevent removal/coalescing of repeated copies.
An observable volatile checksum consumes output. The runner retains both assembly
files, linked disassembly and symbols for inspection. Verification is not timed
and therefore does not inflate copy bandwidth. Runtime counts and zero-live-byte
cleanup assertions are checked for every batch; leak detection remains a separate
sanitizer capability.

## Sampling and artifacts

Case order uses seed 20261030. For each scope there are two warmup pairs, adaptive
calibration up to two million calls per batch, then equally sized paired batches
with alternating adapter/C order and alternating starting side. Fresh fixtures
are used for each batch; repeated calls within a batch reuse source/destination.
Initialization immediately precedes timing, so small cases are warm-cache and
bulk copies have recently touched memory. `CLOCK_MONOTONIC` measures elapsed time;
timer/loop overhead is not subtracted. Compilation, validation and sanitizers are
outside measured time. No samples are discarded as outliers.

Artifacts include `raw.csv` (warmups, calibration, measured pairs, exact counts),
`cases.json`, `summary.json`, `summary.md`, `environment.json`, `commands.json`,
`verification.log`, `sanitizers.json`, `source/`, compiler assembly, disassembly,
symbols and linked-library information. `build/` contains disposable executables.
Source SHA-256 hashes, git base/dirty state, toolchain, flags, CPU, OS, libc,
affinity, cgroup quota and load are recorded. `live_bytes` in reused scopes is
the live fixture during timing; `fixture_live_bytes` after cleanup must be zero.
`peak_bytes` is a data high-water size, not a sum. `metadata_bytes` is the maximum
lifecycle metadata snapshot; it is zero in reused scopes because metadata was
allocated outside their timed intervals (280 runtime metadata bytes on this host).
Loop setup also allocates one experiment-only prepared descriptor outside timing;
that descriptor is not part of runtime counters, and is freed on both sides.
Other `timed_*` counters sum over the whole timed batch. `loop_only` bypasses
accounting inside the timed loop, so its timed copy counter is zero even though
each real loop copies `rows * columns * (8 or 16)` bytes. Setup's validating copy
is outside timing. There are no hidden packing copies or scratch buffers.

Summaries report medians, IQR, MAD, minima/maxima, paired differences and paired
ratios. The 95% percentile interval resamples the paired ratios 5,000 times with
a fixed seed; it describes **within-run** variability, not process/host variation
or a performance certification. Tiny calls need absolute ns differences. These
measurements do not set a tiny-call acceptance budget and do not apply #222's
provisional 10% target as a pass/fail gate. Even favorable lifecycle results do
not establish equality of prepared loops or of the complete generated runtime.
