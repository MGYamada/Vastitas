# Checked source allocator phases — Linux

Full diagnostic record from clean
`f0e0c55d79978d68021ba0ee0831916d1153606d`, submitted in
[PR #366](https://github.com/MGYamada/Vastitas/pull/366).
This is allocation/cost evidence from shared CI, not timing acceptance or native
refinement.

| Provenance | Value |
| --- | --- |
| Source run | [Push workflow 41284566483](https://github.com/MGYamada/Vastitas/actions/runs/41284566483), [Linux job 124783134838](https://github.com/MGYamada/Vastitas/actions/runs/41284566483/job/124783134838) |
| Host | Linux 7.0.0-1017-azure, x86_64, glibc 2.43; shared `ubuntu-latest` runner; no controlled-host claim |
| Compilers | GCC 15.2.0; private Lean runtime build with Clang 21.1.8 |
| Lean | Installed 4.35.0; stock plus private rebuilt-zero / `MI_STAT=2` runtime archives |
| Lean calibration | Same clean `f0e0c55`; complete nine-process / 162-snapshot record retained inside this archive |
| Backend calibration | Same clean `f0e0c55`; complete paired OpenBLAS 0.3.34 calibration retained; sequential LP64, HASWELL |
| Source inputs | 66 repository snapshots, independently matched to the measured Git revision and the retained macOS input set |
| Source commands | 1,663, including exact kernel-stdin hashes, context and raw observations |
| Compact archive | [evidence.zip](evidence.zip), 4,668 members, 64,228,863 bytes |
| SHA-256 | `d99a971d60c35c9e698760e80c3d6aa9270dc75f55e325adabaad9eb66ce972d` |
| Export manifest | [artifact-manifest.json](artifact-manifest.json) |

The downloaded Actions artifact `source-workspace-ubuntu-latest-push`, ID
`13075516860`, is a separate outer ZIP containing the compact archive and manifest.
Its 62,673,815 bytes were checked against GitHub's SHA-256
`79e2d210fb67ff555ea6b329421ff84e21b5bed32e40ddab2f842ad494c32453`
before extracting those two files. The retained inner archive is unchanged.

Canonical public executables use stock Lean and stock BLAS. Private observation
executables select the calibrated archives, with full linker maps and installed
toolchain fingerprints retained. Replaying the record does not execute archived
programs. The later verifier also checks that linked support archives, including
`libInit.a`, use their calibrated installed paths; this strengthens validation
without changing the measured source revision or raw observations.

## Coverage and observations

All twelve tiny/small/bulk, real/complex, padded/unpadded cases cross three Lean
runtimes with two backends. There are **864 normal executions, 72 checked failure
cleanups and 72 canonical public check/build/executions**. The 936 observation
processes produce 9,360 allocator snapshots. Immediate empty repeats at all five
boundaries agree. The 312 `MI_STAT=2` processes supply calibrated normal count and
binned-byte deltas; unsupported counts in the other 624 processes remain null.

For every tested case and both backends, the measured run phase is:

| Operation | Repetitions | Normal allocations | Binned bytes | Current-byte change |
| --- | ---: | ---: | ---: | ---: |
| Generated lifecycle | 1 | 6 | 120 | 0 |
| Generated lifecycle | 2 | 9 | 176 | 0 |
| Generated lifecycle | 17 | 54 | 1,016 | 0 |
| Generated caller-buffer reuse | 1 / 2 / 17 | 3 | 64 | 0 |
| Matched C, either scope | 1 / 2 / 17 | 0 | 0 | 0 |
| Checked failure and cleanup | 1 | 7 | 184 | 0 |

These results agree with the independently retained
[macOS record](../2026-11-01-macos-allocator/RESULTS.md). Lifecycle costs match
`3N+3` objects / `56N+64` bytes for the three measured batch sizes. Reuse's three
objects / 64 bytes belong to the batch wrapper/control path, not each call. C
runs inside the same Lean-hosted fixture after cold generated work; its row is
not standalone C process accounting.

The failure's original five selected objects / 88 bytes omit the actual error
payload: a 16-byte `IO.Error` and a string with 76 requested / 80 usable bytes
(44 UTF-8 bytes including the terminator). Those **two allocations / 96 binned
bytes** explain the full 7 / 184 result; the requested counter changes by 180.
No further normal allocation is unattributed in the four observed phases of the
312 diagnostic processes, and no huge allocation is observed. Final normal
current is 16 in every diagnostic process, matching the persistent Unit result.
Setup releases pre-baseline command arguments; negative current-byte deltas are
retained, not treated as negative allocation.

All 13,536 actual CBLAS calls retain dimensions, layouts, coefficients and event
intervals. The 468 backend-diagnostic processes observe 6,768 pool borrows and
matching returns, plus one 128 MiB mapping per process retained after cold work
until explicit quit. All mappings are released. These are virtual capacities,
not resident peaks or measured packing traffic. Outputs and explicit
arena/backend costs agree across Lean variants and matched C scopes. Overlapping
selected-site, allocator, arena and backend channels must not be summed as
independent costs.

## Verification and limits

The CI runner completed the full experiment, compact export and all 39 then-current
source observation/replay/mutation tests. Local replay independently validated
the downloaded archive, manifest summary and all 66 source snapshots against Git.
The publication tests additionally replay both retained OS archives and reject
foreign linked support libraries as well as foreign runtime paths.
`python3 -m unittest discover -s experiments/source_workspace -p 'test_*.py'`
passed all 41 tests, and the ten `SourceAllocatorRecord` cases also passed with
this Linux archive selected through `VASTITAS_SOURCE_ALLOCATOR_RECORD`.
Dependency-boundary, diff and local Markdown link checks passed.

The allocator observer uses 43,732 static bytes, excluding its code, strings,
alignment, stack and reporting costs. Reporting starts after the final snapshot;
no operation clocks run. Diagnostic counts are not claimed as stock counts.
Requested counters are incomplete/cumulative and raw peaks are not operation
peaks. Startup on the waiting initialization thread, other allocators, backend
packing/static metadata, residency and other source profiles remain outside this
channel. The largest fixture does not establish representative memory-bound
performance. Tiny/bulk budgets, controlled Linux measurement and historical
Stage 1 completion remain open. Hashes establish integrity/correspondence, not
authenticity or native refinement.
