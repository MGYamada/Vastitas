# 2026-10-31: public GEMM performance unmeasured

**No public generated/C timing result is available.** The pinned Lean 4.35.0
executable fails at startup with `error: failed to locate application` in the
available environment. The actual kernel build was attempted and failed with
this diagnostic. Independent Lean acceptance/emission, the public native build,
the benchmark Lean wrapper's compilation/execution, and the generated/C
performance comparison therefore remain unvalidated here. No medians,
dispersion estimates or speed ratios are reported.

The initial experiment was prepared against source base
`25b76687c045a8900167bcc769ce3765729ea0af`, which includes #321 and #327.
The harness and the validation possible in this environment are complete;
the generated measurement path still needs execution on a compatible host.

## Actual validation

The matrix comprises 24 cases: F64/Complex × contiguous/padded ×
overwrite/accumulate × `(M,N,K) = (2,3,4), (17,13,19), (384,320,256)`.
All use explicit alpha; accumulate also uses explicit beta. Native tests use
the pinned sequential LP64 OpenBLAS 0.3.34 and `NativeFast` policy.

| Check | Result |
| --- | --- |
| Rust source-to-public-protocol-8 capture | 24/24 passed; capture deliberately rejects and is not Lean acceptance |
| Actual C adapter versus independent direct-CBLAS baseline | 24/24 passed |
| ASan/UBSan on the same full case matrix | 24/24 passed, fatal diagnostics enabled |
| Exhaustive output, input/padding, recurrence and paired checksum checks | Passed for all native cases and scopes |
| Deliberate input/output/padding corruption and failure-before-write tests | Passed |
| Allocation/free/copy/write/peak-data/metadata and cleanup checks | Passed |
| Optional Python harness guard regressions | 4 passed |
| Private instrumented storage and FFI C compilation | Passed with warnings as errors |
| Existing `scripts/check_gemm_native.py` | Passed, including backend version/ABI/thread rejection |
| `scripts/check_boundaries.py`; Python syntax; diff whitespace | Passed |
| Independent Lean and public generated execution | Unavailable / not validated here |

Native data allocations are exactly three per lifecycle operation and zero in
prepared windows. Arena copies are zero, drops balance allocations, and final
live bytes are zero. Peak matrix capacity ranges from 208 to 4,893,936 bytes
across the tested cases, including padding. These are arena counters, not total
Lean/BLAS/allocator allocation counts. Process peak RSS is collected separately
by the harness; BLAS-private packing/workspace counts remain unmeasured.

LeakSanitizer was explicitly disabled for the recorded native run after a
separate leak-enabled attempt ended with `LeakSanitizer has encountered a fatal
error`. ASan/UBSan success and zero arena live bytes do not substitute for a
successful whole-process leak scan.

Native selftests emit timing fields while checking batching and counters. Those
are correctness diagnostics only, not public performance measurements.

## Reproduction and retained evidence

See the [method and commands](../../README.md). The runner saves toolchain and
host conditions, source and BLAS hashes, source packages, public requests,
command/build/check times and native validation logs. When generated execution
is available, it additionally saves generated code, raw timing pairs and
statistical summaries. Compilation and checking are outside runtime clocks.

The full diagnostic archive for this attempt was retained in the accompanying
downloadable deliverable. It is **not included in this repository addition**;
this page is an aggregate validation summary, not a public raw-data timing run.
The generated comparison must be completed and its evidence retained before
any performance conclusion can be drawn.

No mandatory CI gate or production API was added. This result does not establish
Stage 1 completion, native refinement, #222's performance target or general
C/C++ performance equivalence.
