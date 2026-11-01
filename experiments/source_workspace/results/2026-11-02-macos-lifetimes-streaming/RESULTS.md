# macOS source block lifetimes: large-output profile

This record measures clean `8212d7d0a6720e37913b6d44d5932e8ff263ead8` on
macOS 27.2 arm64. It extends the existing separate streaming profile to all eight
backend/runtime configurations in source-cost schema 4. It contains no operation
timings or controlled-host acceptance claim.

The [complete compact record](evidence.zip) and
[manifest with full replay summary](artifact-manifest.json) preserve:

- Four real/complex, padded/contiguous cases, with 128 / 256 MiB outputs and
  batches 1 and 2; 32 canonical public check/build/executions use stock libraries.
- 256 normal observations, 32 failure-cleanup processes and 1,408 actual CBLAS
  calls, with exact returned code, coordinate/padding checks and resource costs.
- 2,880 calling-thread statistics snapshots across all configurations and
  360 before/after lifetime boundary pairs in the two calibrated lifetime variants.
- 20 actual source packing contracts, checked by 80 additional plain/sanitized
  stock/diagnostic footprint executions.
- Both complete nested allocator calibrations, the backend calibration, linker
  maps, calibrated object/archive fingerprints, source and raw command receipts.
  All 86 source snapshots match the measured Git commit.

The archive has 9,209 members and 34,862,974 bytes. Its SHA-256 is
`1ecf43368d8ebb93d72b56b53a53e3599586bf873f436645b262aebf594d1689`.
The exporter replays both the build directory and compact archive and requires
identical summaries. The 19 actual lifetime record regressions and four complete
source packing regressions pass against this ZIP (23 tests, no skips).

## Observed logical-block costs

These are private lifetime-runtime measurements; the independent `MI_STAT=2`
channel reconciles their phase allocation and live-byte changes. Values below
agree across all four cases and both backends in this run.

| Run scope | Allocations / frees | Requested / acquired / released bytes | Peak usable bytes above entry |
| --- | --- | --- | --- |
| Generated lifecycle, 1 operation | 5 / 5 | 104 / 104 / 104 | 72 |
| Generated lifecycle, 2 operations | 7 / 7 | 144 / 144 / 144 | 72 |
| Generated caller-buffer reuse, either batch | 3 / 3 | 64 / 64 / 64 | 48 |
| Matched C, either scope/batch | 0 / 0 | 0 / 0 / 0 | 0 |
| Checked generated failure | 7 / 7 | 180 / 184 / 184 | 136 |

The failure includes two actual error payload objects, with 92 requested and
96 usable bytes, separately from the already selected error result. These
channels overlap: do not add selected-site, statistics and lifetime counts.
The C comparator is Lean-hosted and each process first executes cold generated
work; its zero run-scope count is not a zero-startup or standalone-C heap claim.

Before cold execution, the observer retains 11,130 or 11,131 cumulative
allocations and 2,986 live blocks, with 124,768 or 124,776 live usable bytes.
The global peak is 125,040 or 125,048 bytes. These process-specific states include
initialization and command arguments; they are not normalized away. Releasing
preexisting arguments during setup decreases live bytes while still allocating.
The run interval peak remains distinct from the larger initialization peak.

The lifetime observer occupies 4,194,417 declared static bytes and its phase
storage occupies 1,208 bytes, separately from the existing 43,732-byte statistics
observer. Native arena data and backend workspace are different channels.
Do not add independent subsystem peaks as a simultaneous whole-process peak.
Physical allocator backing/RSS, libc/GMP and other allocator traffic, reporting,
process teardown, stock timing, full cost attribution and Fast like C acceptance
remain outside this result.
