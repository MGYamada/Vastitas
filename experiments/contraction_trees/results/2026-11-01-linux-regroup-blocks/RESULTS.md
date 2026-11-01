# Full Linux contraction-tree measurements after short-axis regrouping

All twelve public source check/build/executions and the native/output/cost
validations passed at clean main `7486d2ca7f8f9bb9cd2bc4d77335b47e79ebf28c` after PR #357.
**Fast like C acceptance remains open.** This is a shared GitHub-hosted Linux
measurement against the existing contiguous-block C comparator, not a controlled
performance acceptance run or a paired old/new optimization experiment.

The [#356 production-Unit record](../2026-11-01-linux-unit-result/RESULTS.md),
[older Linux block-copy record](../2026-10-31-linux-block-copy/RESULTS.md), and
[Apple M4 native-only A/B record](../2026-11-01-macos-regroup-blocks/RESULTS.md)
remain unchanged. The new hosted run and #356 both report an EPYC 7763, but
separate shared-runner jobs with the same CPU model are not a matched same-host
experiment. Other records have different CPUs; the M4 A/B excludes Lean/FFI.
No cross-run ratio is used to estimate the effect of #357.

## Execution and provenance

- [Successful run 41290985225, job 124802014404](https://github.com/MGYamada/Vastitas/actions/runs/41290985225/job/124802014404).
- Measured **clean main**: `7486d2ca7f8f9bb9cd2bc4d77335b47e79ebf28c`.
- Launcher-only commit: `ab015081534035ad34bea7c4dfac469b8fac79cf`. The GitHub connector
  has no workflow-dispatch operation. A separate measurement branch reused the
  existing workflow, selected `full`, and pinned `actions/checkout` to the exact
  main SHA above. The launcher's workflow changes are **not** part of the measured
  tree or this publication's production workflow.
- [launch-provenance.json](launch-provenance.json),
  [launcher-workflow.yml](launcher-workflow.yml), and
  [measured-workflow.yml](measured-workflow.yml) preserve that distinction and
  the local toolchain blocker that led to hosted execution.
- [launcher-git-objects.json](launcher-git-objects.json) retains the exact launcher
  commit and its three workflow-path tree objects. The verifier checks their Git
  object hashes from the pinned commit through to the workflow blob. Reproduction
  therefore does not require retaining or fetching the temporary launcher branch.
- Harness interval: `2026-11-01T09:00:45.329136+00:00` through `2026-11-01T09:06:26.071193+00:00`.
- Twelve canonical public check/build/executions; twelve independent kernel
  check/emit paths and exact-instruction wrappers; 24 optimized/sanitized native
  validations, including Linux ASan/UBSan/LSan; 288 separate exhaustive generated/C
  verification executions. The workflow also built the pinned kernel/frontend
  and passed all eight existing harness tests.
- **2,622 raw rows = 288 warmup + 750
  calibration + 1,584 measurement rows**: 1,311
  generated/C pairs, 72 case/scope groups, eleven measurement pairs per group.
  Every raw row, including noisy and short batches, is retained.

Host: **AMD EPYC 7763 64-Core Processor**; platform `Linux-7.0.0-1017-azure-x86_64-with-glibc2.43`. CPU
0 was selected from `[0, 1, 2, 3]`. Affinity does not
provide host isolation, fixed frequency, or a dedicated CPU. The environment
record includes load, cgroup limits, compiler versions, source/binary/backend
hashes and the final unchanged-input check. GCC/C flags are
`-std=c11 -O3 -fno-lto -Wall -Wextra -Werror`. Rust 1.99.1 and Lean 4.35.0 are pinned.
Both paths use NativeFast, one BLAS thread, identical physical layouts and the
same sequential LP64 OpenBLAS 0.3.34 HASWELL archive, SHA-256
`1ca3e930bb5e5ec46000ea7978e019abb3076d31eb56bc382b030ac46051fcaa`.

While the experiment was running, main advanced to
`6ac794c46c06f83ea0b149539b2441a062ca6165` (#366). All 47 archived repository
input files still match that commit byte for byte; production compiler/runtime
sources and this harness did not change. The publication integrates its concurrent
ledger additions, but **the measured revision remains `7486d2c`**, not #366 or
this publication commit.

## Where the post-optimization costs remain

The source dispatcher coalesces the common first axis at 16–64 bytes. Its
condition selects tiny F64 (16 bytes), tiny complex (32 bytes), and small F64
(56 bytes), for both layouts. Small complex (112 bytes), bulk F64 (192 bytes)
and bulk complex (384 bytes) retain the cell loop. This classification follows
from the archived source and dimensions; it is not a new instruction-counter
measurement. All twelve coordinate, padding, mutation and paired-cost checks
passed, including the fallback cases.

Each table entry is the median of eleven **within-pair generated/C ratios**,
with its paired 95% bootstrap interval in brackets. A value above one means
that generated execution took longer in that scope. Intervals describe this run,
not host/process uncertainty. `regroup3_adapter` excludes Lean/FFI;
`reused_buffers` includes all four emitted FFI calls and adapter preflight;
`lifecycle` includes arena allocation/initialization/assertions/cleanup.
The diagnostic scopes still execute the complete numerical schedule.

| Case | Regroup path | regroup3_adapter | reused_buffers | lifecycle | Lifecycle paired delta (ns) |
| --- | --- | ---: | ---: | ---: | ---: |
| tiny-f64-p0 | short block | 1.6373 [1.6113, 1.7222] | 1.4634 [1.4090, 1.5022] | 1.4847 [1.3755, 1.5012] | 517.0 |
| tiny-f64-p1 | short block | 1.5901 [1.5767, 1.6104] | 1.4334 [1.3580, 1.4480] | 1.4930 [1.4802, 1.6344] | 592.9 |
| tiny-complex-p0 | short block | 1.7020 [1.6763, 1.7408] | 1.4270 [1.2383, 1.4637] | 1.4529 [1.4398, 1.4668] | 542.7 |
| tiny-complex-p1 | short block | 1.7319 [1.7070, 1.7722] | 1.4549 [1.3867, 1.4879] | 1.4377 [1.4115, 1.5738] | 994.4 |
| small-f64-p0 | short block | 1.2545 [1.2337, 1.2899] | 1.2135 [1.1096, 1.2418] | 1.1260 [1.0376, 1.2556] | 432.9 |
| small-f64-p1 | short block | 1.2519 [1.1400, 1.3675] | 1.1141 [1.0252, 1.1583] | 1.2693 [1.0625, 1.9155] | 921.6 |
| small-complex-p0 | cell fallback | 1.3241 [1.3002, 1.5265] | 1.1003 [1.0632, 1.1116] | 1.1184 [1.0574, 1.1494] | 715.9 |
| small-complex-p1 | cell fallback | 1.5388 [1.4365, 1.5946] | 1.0852 [1.0497, 1.1122] | 1.1096 [1.1010, 1.2056] | 683.8 |
| bulk-f64-p0 | cell fallback | 0.9895 [0.9738, 1.0049] | 0.9542 [0.8235, 1.0213] | 0.9590 [0.9322, 1.0825] | -29950.6 |
| bulk-f64-p1 | cell fallback | 1.0163 [0.9967, 1.0420] | 0.9842 [0.8662, 1.0293] | 1.0145 [0.9978, 1.0389] | 13379.8 |
| bulk-complex-p0 | cell fallback | 1.1055 [1.0749, 1.1128] | 1.0101 [0.9741, 1.0689] | 1.0003 [0.9864, 1.0110] | 571.0 |
| bulk-complex-p1 | cell fallback | 1.0545 [1.0369, 1.1126] | 1.0138 [0.9864, 1.0825] | 1.0063 [0.9689, 1.0315] | 12951.0 |

Tiny lifecycle ratios are **1.4377–1.4930**, with paired overhead
**517–994 ns**; reuse ratios are
**1.4270–1.4634**. Small F64 regroup/reuse/lifecycle ratios are
**1.2519–1.2545 / 1.1141–1.2135 /
1.1260–1.2693**, respectively. Bulk lifecycle ratios are
**0.9590–1.0145**. These are the measured post-merge relationships to
C at the three layers. Tiny lifecycle overhead remains material. Small padded
F64 lifecycle has a wide interval reaching 1.9155; bulk complex contiguous
regroup is 1.1055 with interval 1.0749–1.1128. These unfavorable observations
remain in the record. Functional/cost fallback regressions passed; absence of a
performance regression relative to the old implementation is not established.
These measurements do not quantify a before/after improvement: a matched
old/new run on the same controlled host has not been performed. Scoped medians
cannot be subtracted to identify FFI or allocator overhead.

[summary.md](summary.md) and [summary.json](summary.json) retain all six scopes,
absolute per-operation time distributions, separate-median ratios, paired deltas,
MAD/quartiles/extrema and bootstrap intervals. Separate-median ratios and paired
medians are distinct statistics; neither may be selected merely to claim parity.

## Allocation and data movement

Every generated/C pair agrees on hashes, allocations/frees, writes/copies,
peak arena data/metadata and cleanup. The verifier independently reconstructs
costs from dimensions and padding. Per lifecycle: six data allocations/frees and
two metadata allocations; live arena bytes after cleanup are zero. Timed reuse
and adapter scopes allocate/free no data or metadata. The 280-byte peak metadata
value is specific to the recorded x86-64 ABI.

| Case | Peak arena data bytes | Copied bytes per four-operation schedule | Schedule writes | Full lifecycle writes |
| --- | ---: | ---: | ---: | ---: |
| bulk-complex-p0 | 2762752 | 1081344 | 2703360 | 6017120 |
| bulk-complex-p1 | 2825248 | 1081344 | 2703360 | 6079616 |
| bulk-f64-p0 | 1381376 | 540672 | 1351680 | 3008560 |
| bulk-f64-p1 | 1412624 | 540672 | 1351680 | 3039808 |
| small-complex-p0 | 45248 | 15680 | 37856 | 96752 |
| small-complex-p1 | 53824 | 15680 | 37856 | 105328 |
| small-f64-p0 | 22624 | 7840 | 18928 | 48376 |
| small-f64-p1 | 26912 | 7840 | 18928 | 52664 |
| tiny-complex-p0 | 3248 | 1024 | 2624 | 6976 |
| tiny-complex-p1 | 6592 | 1024 | 2624 | 10320 |
| tiny-f64-p0 | 1624 | 512 | 1312 | 3488 |
| tiny-f64-p1 | 3296 | 512 | 1312 | 5160 |

All counted arena allocations and explicit data movement match the contract;
no additional counted arena copy or allocation was observed.
Arena counts exclude general Lean heap/allocator internals and BLAS-private
workspace. `process_maxrss_kib` may include the launcher's pre-exec footprint;
it is not isolated executable heap accounting. The preserved counts therefore
do not satisfy total-allocation/backend-workspace acceptance.

## Retained data and independent audit

[evidence.zip](evidence.zip) is the original compact Actions artifact
`13076823726`: 445,202 bytes, SHA-256
`c7005be138e3e096ed9564fcd526d5ba7ceeebc3c7f0765941e674f66e7b476d`. It retains every one of its
177 members: commands, generated packages/wire, kernel
responses, emitted source, wrappers, private runtime sources, exact input
snapshots, validation, raw CSV, compile times and statistics. Nine plain copies
are byte-identical to the archived originals. [artifact-manifest.json](artifact-manifest.json)
records every member hash and service provenance.

The separate symbol/disassembly artifact `13076589328`
(60,622,521 bytes; service SHA-256
`8c0f4bde1568ec741fc16db80c541f0b1325a833f97b55cfc2a61ee38da40022`) was not downloaded or
independently inspected. Compact records retain linked-library output plus
hashes/lengths of the large logs. This is not an instruction-level audit. Actions
retention is fourteen days; the compact original ZIP is preserved here.

[verify.py](verify.py) independently checks archive digest/CRC/inventory, nine
plain copies, 47 source snapshots
against the exact measured Git tree, both workflow snapshots against their own
Git commits (using the preserved launcher objects), every raw pair and dimension-derived cost, command/CSV agreement,
all native/verification results and every generated-wrapper/canonical result.
It recomputes all 72 statistical groups and 5,000-resample bootstrap intervals
without importing the producing harness. [independent-audit.json](independent-audit.json)
is the retained audit output. The only nonzero command results are the twelve
intentional rejecting wire-capture invocations; they grant no acceptance.

```sh
# The measured main commit must be available; no launcher ref is needed.
python3 experiments/contraction_trees/results/2026-11-01-linux-regroup-blocks/verify.py
```

72 of 72 final calibration pairs reached
5 ms on both sides. 116 later
measurement batches fell below that target; the minimum was
3,948,092 ns. All are retained. The target is
calibration guidance, not a filtering rule or a guaranteed sample duration.

These results support the bounded implemented source/native path and its
visible cost contract. They do not prove native refinement, floating-point
field laws, a causal optimization speedup, or Fast like C. Dedicated controlled
host measurements, a predeclared tiny-call absolute budget, unresolved overhead,
and complete allocation/backend-workspace attribution remain open in #179,
#183 and #222. No issue or acceptance gate is closed by this record.
