# Checked source costs after Unit cleanup — Linux

This full schema-3 record measures clean
`84b0c115f1a003edf52d4634c9dbebbbf6531b18`. It includes the Unit-only
cleanup change subsequently merged in [PR #378](https://github.com/MGYamada/Vastitas/pull/378)
as `77bdd093897a8cd9a66daf6cae0e904dd58570ae`. Publication does not relabel the
measured revision or the [older packing record](../2026-11-01-linux-packing/RESULTS.md).

| Provenance | Value |
| --- | --- |
| Host | `Linux-7.0.0-1017-azure-x86_64-with-glibc2.43`; shared GitHub runner |
| Source CI | [Push run 41307639076](https://github.com/MGYamada/Vastitas/actions/runs/41307639076) |
| Compiler/runtime | Lean 4.35.0; installed stock and private rebuilt-zero / `MI_STAT=2` archives |
| Backend | Pinned sequential LP64 OpenBLAS 0.3.34; exact stock/diagnostic archives retained in the nested calibration |
| Calibration revisions | Both backend and Lean calibrations measure the same clean `84b0c11` head |
| Source provenance | All 81 repository snapshots independently match Git; 1,931 retained commands |
| Compact archive | [evidence.zip](evidence.zip), 10,903 members, 72,024,411 bytes |
| SHA-256 | `c74c1723ebbe9d67c6cb428553eeba899e1c6161db95287af2536558c494d550` |
| Receipts | [Export manifest](artifact-manifest.json), [GitHub artifact provenance](github-artifact.json) |

## Observed coverage and costs

All twelve tiny/small/bulk real/complex padded/unpadded cases cross two backends
and three Lean runtimes: **72 canonical public check/build/executions, 864 normal
observations, 72 checked failure cleanups and 13,536 actual CBLAS calls**.
The 936 observation processes retain 9,360 allocator snapshots. Canonical public
executables use stock Lean and stock BLAS; diagnostic runtimes only appear in
private observed executables.

Actual source addresses, arguments and event intervals bind every diagnostic
packing route. The 66 observed source packing contracts each pass plain
and ASan/UBSan executions against both exact backend archives, totaling
**264 additional footprint executions**. Numerical output, padding, arena
traffic, selected objects and backend logical costs agree between generated and
matched C work, including caller-buffer reuse.

The diagnostic calling-thread run phases observe:

| Scope | Normal allocations | Binned bytes |
| --- | ---: | ---: |
| Lifecycle, 1 repetition | 5 | 104 |
| Lifecycle, 2 repetitions | 7 | 144 |
| Lifecycle, 17 repetitions | 37 | 744 |
| Caller-buffer reuse, each recorded batch | 3 | 64 |
| Matched C run phase, each recorded batch | 0 | 0 |
| Checked failure | 7 | 184 |

The lifecycle counts include one fewer 16-byte generated result constructor per
iteration than the older `finally` records. The failure count includes the two
actual error-payload allocations / 96 binned bytes. No normal count or binned
byte remains unattributed in these recorded diagnostic phases. Selected-site and
allocator observations overlap and must not be added together. Stock/rebuilt-zero
normal-count summaries remain unavailable; these are not stock total-heap counts.
Cold generated execution, setup and cleanup retain their own charged phases.

The diagnostic backend retains a 128 MiB virtual mapping after cold execution
and releases it at explicit shutdown. It is backing capacity, not RSS or a
meaningful whole-process peak. Named pool metadata and the separate observer
objects remain charged in the raw record.

## Verification and limits

The CI job passed full execution, archive replay and its mutation tests. Local
independent ZIP replay reproduced the export manifest exactly; the downloaded
outer ZIP matches GitHub's digest, and all source snapshots match the measured
Git commit. Both OS source-input maps are identical. The later verifier reads
archived bytes without executing archived code.

Operation clocks are disabled. Startup on Lean's waiting initialization thread,
other allocators, complete requested-byte/general peak accounting, shortcut
internals and unmeasured source paths remain excluded. Fewer diagnostic object
allocations do not establish a timing improvement. The standard matrix remains
small; see the separate large-output profile in the [experiment guide](../../README.md).
Tiny-call budgets and controlled-host measurements remain open in the
[Stage 1 completion gate](../../../../docs/stage1-completion.md).

Publication validation passed all 71 source replay/mutation tests with the Linux
streaming record selected, including explicit replay of both post-cleanup and
both streaming exports. This later verification preserves the original measured
heads, source snapshots and raw observations.
