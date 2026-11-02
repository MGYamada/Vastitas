# Optional public GEMM / equivalent C experiment

This experiment extends the measurement conventions of
[`storage_copy`](../storage_copy/README.md) to **public protocol 8** after #321.
It adds no production API, performance threshold or package gate. A separate
Linux smoke workflow validates changes to this experiment on both push and
pull_request, and can also be dispatched manually. It does not close #222,
establish Stage 1 completion, prove native
refinement, or establish general C/C++ performance equivalence.

Historical **generated/arena-C** measurements (shared runtime checks, not standalone C): [full Linux run with raw pairs and remaining overhead](results/2026-10-31-linux-full/RESULTS.md).
Recorded validation: [Linux generated-path smoke passed](results/2026-10-31-linux-smoke/RESULTS.md);
[original unavailable-toolchain attempt](results/2026-10-31-linux-unmeasured/RESULTS.md).
The smoke validates execution and output/cost contracts, without a performance
acceptance claim. Diagnostic archives are retained separately; this repository
addition publishes source and aggregate validation records.
Native C correctness is distinct from successful public Lean acceptance and
generated execution. A failed toolchain never produces substitute performance
numbers from the C adapter tests.

## Reproduce

Linux x86-64, Python 3, the repository-pinned Rust and Lean toolchains, a C11
compiler and the **same sequential LP64 OpenBLAS 0.3.34 archive** for all three arms:

```sh
python3 scripts/build_openblas.py --prefix /tmp/gemm-openblas --jobs 4 --target HASWELL
cargo build --release --locked
python3 experiments/public_gemm/test_harness.py
python3 experiments/public_gemm/run.py \
  --prefix /tmp/gemm-openblas --output /tmp/gemm-run
```

Select a supported OpenBLAS CPU target for the host; the example requires Haswell
instructions. Never reuse this archive on an incompatible CPU. `--cc /path/to/cc`
selects the same host C compiler for the baseline, storage, numerical adapter,
FFI and generated consumer. The existing kernel builds with its pinned Lean
toolchain. The output directory must not exist.

`--smoke --samples 6 --target-ms 0.1` runs only the two smaller sizes and is **not
performance evidence**. `--cpu N` selects an allowed CPU (default: first allowed).
Default: 12 three-arm groups per scope, rotating through all six execution
orders, with adaptive batches targeting at least 5 ms for every arm, at most 1,000,000 operations. Use an otherwise idle host;
the runner does not control frequency, turbo, other processes or virtualization.
All thread environment variables are set to one and the adapter rejects a
non-sequential/incorrect-version/ILP64 backend. Actual backend configuration,
parallel mode and thread count are also printed by native validation.

The dedicated workflow keeps push and pull-request runs on `smoke`. Manual
dispatch accepts `profile=full` to execute all 24 cases with 12 three-arm groups
per scope and a 5 ms calibration target, including the bulk dimensions. For
example, select the reviewed revision explicitly:

```sh
gh workflow run public-gemm-experiment.yml --ref REVIEWED_REF -f profile=full
```

Both profiles retain sanitizer checks, the 45-minute job cap and diagnostic
artifacts for 14 days. Full hosted measurements are exploratory: shared-runner
noise, launcher-inclusive RSS and uninstrumented backend workspace still prevent
controlled-host performance acceptance. Preserve selected raw pairs and exact
revision/environment records before the temporary artifacts expire.

ASan/UBSan validation runs separately for every case before timing, with fatal
diagnostics. `--no-leak-sanitizer` explicitly disables LSan when the host cannot
inspect processes; it does not disable ASan/UBSan. The pinned BLAS archive itself
is not sanitizer-instrumented. `--allow-unavailable` saves an **unmeasured** report
if the pinned Lean kernel cannot build, after requiring frontend capture and
native correctness/sanitizer tests. It does not ignore a checker rejection,
generated-code build failure, runtime failure or output/cost mismatch.

## Data and numerical contract

24 cases: binary64 and interleaved binary64 complex × contiguous and padded ×
overwrite and accumulate × `(M,N,K) = (2,3,4), (17,13,19), (384,320,256)`.
Every case is rectangular with three different dimensions. All operations are
column-major, N/N, `NativeFast`, with explicit alpha. Accumulate also has explicit
beta; overwrite fixes beta to zero and omits its source operand as required by
the public syntax. Real alpha/beta are `1.5 / 0.5`; complex values are
`(0.75 - 0.5i) / (0.5 + 0.25i)`. These are exactly representable machine literals,
not a claim of exact field arithmetic.

Padded A/B/C use offsets of 1/2/3 elements and leading dimensions of
rows + 2/3/4 respectively, plus three trailing elements. Offsets in public
`layout` are **bytes**. Every physical allocation is first filled with a sentinel;
logical A/B and accumulate C are then filled, with two distinct sparse corner
updates in each input. Thus dimensions, offsets, imaginary components and beta
affect observable results. Overwrite must replace its destination sentinel.
The full-buffer sentinel initialization is present in the actual `.vast`
program and on the C side, and is included in lifecycle measurements.

The initial matrix is the same for all three arms. In reused scopes, repeated
accumulate calls deliberately implement the same recurrence
`C[t+1] = alpha*A*B + beta*C[t]`. C is **not reset inside the timed region**;
the oracle verifies the final recurrence at the actual repetition count.
Both chosen beta magnitudes are below one, avoiding overflow from calibration.
No transpose/adjoint, zero-size/zero-inner, arbitrary scalar expression, computed
coefficient loan, GPU or dynamic-shape performance is covered by this experiment.
Those are separate profiles; #321's computed-coefficient correctness remains
covered by the repository's existing source tests.

## Public generation and measurement boundaries

For each case, the runner writes a real source package and obtains its wire
request from the Rust frontend through a **deliberately rejecting** capture
adapter, as in the repository's source regressions. Capture is never acceptance.
The identical protocol-8 request must then pass the real independent Lean
`check` and `emit` entries. The normal `vastitas check`, `vastitas build` and
unmodified executable are also executed as untimed validation.

The complete emitted source is preserved as `Generated.lean`. `Main.lean` wraps
its exact resource instructions in experiment-only loops. It preserves every
allocation, fill, store, GEMM operand, drop and the emitted cleanup/error envelope. It omits
only the terminal print of the constant pure result `0` from timing. The parser
fails closed on unfamiliar instructions, branches, extra GEMMs or changed
cleanup. This instrumentation is an experiment, not a new compiler entry/API.

| Scope | Timed work | Outside its clock |
| --- | --- | --- |
| `lifecycle` | Generated resource execution via Lean/FFI: arena creation, allocation, full initialization, physical preflight, GEMM, constant-size observation, drop/close, arena finalization and counter aggregation; arena-C retains that machinery, while plain C uses aligned allocation/direct CBLAS/free | Process/Lean startup, one backend warmup, compilation/checking, exhaustive verification and reporting |
| `prepared_call` | Repeated emitted `gemmScaled`, including Lean loop/FFI, physical preflight, BLAS and adapter write accounting; arena-C loops over its checked CBLAS boundary; plain C calls CBLAS directly | Allocation, initialization, verification, cleanup |
| `blas_kernel` | Sum of clocks immediately around the **actual CBLAS calls** made by the prepared emitted path and both C paths | All preflight, FFI/loop/accounting work, initialization and cleanup |

`blas_kernel` is a projection of actual calls into the same backend, **not** a
claim that the public runtime has a preflight-free production entry point.
Each kernel interval includes timer cost; the timer/loop overhead is never
subtracted. Tiny-call kernel results can be dominated by this instrumentation.
Do not subtract scope medians to estimate an isolated overhead.

The benchmark uses private copies of the native and numerical Lake packages.
`probe.c` includes the unmodified production storage source for access to arena
contents, and wraps new/drop/delete for observation and accounting. The numerical
copy adds CBLAS clock wrappers. Production source and APIs remain untouched.
Generated and arena-C get the same hooks, allocator, representations, layout checks,
backend check, write counters, cleanup and C compiler. No LTO or fast-math is
enabled. The generated consumer uses `-O3`; its own ordinary Lean loop/FFI costs
remain part of the first two scopes.

The arena-C arm separately initializes the case from `case.h`, checks the finite
nonempty N/N literal-coefficient contract, and directly calls CBLAS. It **does not
call `vgemm_execute_scaled`**. Its physical layout and write-budget primitives
are shared with the adapter; disjoint allocation IDs certify its output
separation for this fixture. It is neither an independent proof of those shared
checks nor an optimized alternative arena/allocator implementation. Static
dimensions and coefficients are available to the C compiler just as to the
public source generator; compiler specialization differences are not concealed.

The [standalone plain-C arm](../plain_c/README.md) links no Vastitas or Lean
runtime. It validates the fixed fixture/backend once, then uses 64-byte-aligned
allocation, the same full initialization/observations and direct CBLAS without
per-call arena preflight or cost counters. Its ordinary-C lifecycle and prepared
scope are the Fast-like-C comparator. The arena arm remains useful for attributing
codegen/FFI overhead. All three use the same backend, compiler and output oracle.

## Correctness and costs

Outside timing, every physical input, output and padding component is inspected.
Inputs and padding must be bit-identical. The output oracle uses a separately
written rank-one-plus-sparse-update identity and a closed-form accumulate
recurrence in `long double`; small products additionally check that identity
against a conventional triple-loop calculation. Output components must be finite
and within `32 * DBL_EPSILON * (K+1) * max(1, abs(expected_component))`. This is a
declared finite test tolerance, not a proved floating-point error bound. Real and
imaginary components are tested separately, and paired results must also have
identical checksums. Deliberate input, output and padding corruption must be
detected; an invalid/aliased output call must fail before writes or accounting.

Lifecycle receives exhaustive checking before and after each scope's timing
series, and every measured lifecycle operation gets an O(1) volatile observation.
Prepared batches get exhaustive verification after every batch. Native selftests
exercise both the actual adapter and the independent C boundary in all scopes.
Generated/arena-C allocation, copy, write, peak-data and metadata counters must
agree. A separate instrumented plain-C executable must match the data costs;
its stack pointer table needs no heap metadata. Plain-C timing cost fields are
blank (unobserved), not zero. Every diagnostic replay must leave zero live data
bytes and equal allocations/frees; its timings never enter performance summaries.

`peak_data_bytes` is the maximum simultaneous matrix allocation capacity,
including padding; it is not summed over repetitions. `peak_metadata_bytes` is
the arena metadata high-water snapshot. `timed_*` fields describe the operation
window (the whole lifecycle or the repeated prepared calls); in `blas_kernel`
the counter updates themselves are outside the inner clock. Prepared scopes
must allocate/copy zero matrix bytes in that window. Initialization writes,
GEMM writes and copies are distinguished: writes are not reported as copies.

These exact arena counters **do not count Lean object allocations, libc allocator
overhead or BLAS-private packing/workspace**. `process_maxrss_kib` retains
`getrusage(RUSAGE_SELF).ru_maxrss` separately for every sample. Linux preserves
resource usage across `execve`, so this diagnostic can include the launcher's
pre-exec memory footprint as well as executable startup/warmup/code/shared
pages. A fresh subprocess does not isolate the executable's memory high-water
mark ([Linux getrusage(2)](https://man7.org/linux/man-pages/man2/getrusage.2.html)).
The value is neither an exact heap counter nor an isolated Lean/BLAS allocation
measurement, and is not required to match across implementations. It cannot localize
BLAS-private allocation counts or packing traffic. Those remain unmeasured;
zero arena copies is not a claim of zero backend packing. The same statically
linked BLAS archive/hash controls the backend across all three arms.

## Sampling, latency and retained evidence

Case order uses seed 20261031. Each group runs three fresh processes with equal
repetitions, cycling through all six implementation orders. Each process performs
one complete untimed lifecycle with its own backend before measurement. Six
additional warmup groups precede calibration. Fresh initialization
means recently touched inputs; this is not a cold-cache/DRAM experiment. No sample
is discarded. All measurement hosts and batch sizes require inspection before
interpreting ratios, especially on shared or throttled machines.

The summary reuses #283's median, IQR, MAD, extrema, paired differences, paired
ratios, and 5,000-resample paired percentile interval. Schema 2 reports
generated/plain-C, generated/arena-C and arena-C/plain-C separately. Only generated/plain-C is the equivalent-C comparator. These
statistics do not establish a performance gate; the interval concerns within-run
variability only. Historical two-arm summaries keep their original schema.

Artifacts include source packages, protocol requests and checker responses,
unmodified emitted Lean and benchmark wrappers, private runtime sources,
source/binary/BLAS hashes, flags, toolchain/CPU/OS/libc/affinity/cgroup/load
information, raw warmup/calibration/measurement rows, checksums and counters,
native validation/sanitizer logs, command logs, disassembly/symbols and summaries.
Large inspection outputs are retained once in per-case text files; command logs
record their paths, byte counts and SHA-256 hashes. JSON snapshots are replaced
atomically so an interrupted run preserves the last complete diagnostic record.
`compile-times.json` reports frontend capture, Lean checking, checking+emission,
normal CLI check/build, harness native compilation and dependency builds
**separately from all runtime clocks**. These are wall times including process
startup and existing build-cache state; the first build and reused builds are
not pooled. The runner never subtracts a guessed compiler/checker latency from
runtime. Build outputs under `.lake` and native-test executables are disposable.
