# Full Linux tree run with the production Unit-result helper

Actual generated execution, native validation and paired output/cost checks
passed. **Performance acceptance remains open.** This run includes the merged
production Unit-success sharing change and the contiguous-block C baseline.
Tiny and small operations still have material overhead; bulk medians are close
to C within this run. Shared-host uncertainty prevents a performance-gate pass.

The [earlier block-copy record](../2026-10-31-linux-block-copy/RESULTS.md) and
[original coordinate-copy record](../2026-10-31-linux-full/RESULTS.md) remain
unchanged. Those runs used different CPU models from this run. These data do not
isolate the timing effect of Unit-result sharing, and lower scoped allocation
counts alone are not timing evidence.

## Revision and retained evidence

- [Successful run 41264519762, job 124724436013](https://github.com/MGYamada/Vastitas/actions/runs/41264519762/job/124724436013).
- Measured **clean** commit: `3e3157a19ad3dfcae8c265fa4de68dd097138c38`,
  after PR #353's production helper and PR #354's acceptance map, before #355.
- Harness interval: 2026-11-01 02:20:12–02:25:48 UTC.
- Twelve canonical public check/build/executions, twelve independent kernel
  check/emit executions and twelve wrappers preserving the exact emitted resource
  instructions. Twenty-four native builds/executions cover optimized and
  ASan/UBSan/LSan validation for every case.
- **2,626 raw rows = 288 warmup + 754 calibration + 1,584 measurement rows**:
  1,313 generated/C pairs, 72 case/scope groups, eleven measurement pairs per
  group. An additional 288 exhaustive generated/C verification executions ran
  outside timing. Native selftest records are separate from timings.
- Compact original artifact `13066274753`: **442,481 bytes**, SHA-256
  `b328544ddd37cef77ddc27a592d97271ba550b94f41cc1bdaa705471f6277293`.
  [evidence.zip](evidence.zip) retains all 176 members: command logs, public
  packages/wire, returned generated source, wrappers, instrumented runtime copies,
  source snapshots, raw rows, validation and summaries. Nine convenient plain
  copies match their archived bytes. [artifact-manifest.json](artifact-manifest.json)
  records every member's hash and the service provenance.
- Separate large inspection artifact `13066713674`: 60,592,056 bytes, service
  SHA-256 `6d6571a6e3244d4eaae2f0985c01b95c2d61247ca2a99b7cfa478748719a5e5c`.
  It was **not downloaded or independently inspected**. The compact archive
  retains linked-library output and hashes/lengths of large symbol/disassembly
  logs; these do not replace instruction-level inspection. Workflow retention
  is fourteen days; the compact original ZIP is retained here independently.

The host was an **AMD EPYC 7763** Microsoft virtual machine, Linux
7.0.0-1017-azure/glibc 2.43. CPU affinity selected CPU 0 from `[0,1,2,3]`; this
is not an isolated controlled CPU. Host load averages are recorded before/after.
Tools: GCC 15.2.0, Rust 1.99.1, Lean 4.35.0 Release (`eb6cafb`). Flags were
`-std=c11 -O3 -fno-lto -Wall -Wextra -Werror`. Both implementations used
NativeFast and the same sequential LP64 OpenBLAS 0.3.34 HASWELL archive,
SHA-256 `1ca3e930bb5e5ec46000ea7978e019abb3076d31eb56bc382b030ac46051fcaa`.
Neither a different algorithm nor a weaker per-element C copy was substituted.

## Independent consistency audit

[verify.py](verify.py) rechecks the original ZIP digest/CRC/member inventory, all
nine plain copies, all 46 archived source snapshots against the exact measured
Git commit, every raw pair and its dimensions-derived cost equations, command
stdout/CSV agreement, all native/verification output and cost pairs, and all
twelve emit responses/canonical results/generated-wrapper instruction sequences.
The recorded 51-input stability guard passed. Medians, quartiles, extrema, MAD,
paired deltas/ratios, separate-median ratios and 5,000-resample paired bootstrap
intervals were independently recomputed. Only twelve intentional rejecting
frontend-capture commands exited nonzero; actual acceptance/build/execution and
inspection commands passed.

With the measured Git commit available locally, run:

```sh
python3 experiments/contraction_trees/results/2026-11-01-linux-unit-result/verify.py
```

The standard-library audit writes no project files and rebuilds nothing.
Compilation/acceptance time is recorded separately from operation clocks.
Timed lifecycle rows use lightweight output assertions; exhaustive buffer,
padding and mutation checks are separate verification/selftest executions.
This consistency audit is not a proof of native refinement.

## Lifecycle and reuse observations

Times are medians in microseconds. The paired ratio is the median of eleven
within-pair generated/C ratios; its interval is a within-run paired bootstrap
interval, not host/process uncertainty. The final column is the distinct ratio
of the two separate medians. Ratios above 1 mean generated execution took longer
than the matched block-copy C implementation in that scope.

| Case / scope | Generated µs | C µs | Paired ratio | 95% interval | Separate medians |
| --- | ---: | ---: | ---: | --- | ---: |
| bulk-complex-p0 / lifecycle | 1820.112 | 1804.232 | 1.0164 | 0.9856–1.0685 | 1.0088 |
| bulk-complex-p0 / reused_buffers | 824.430 | 813.774 | 0.9876 | 0.9302–1.0247 | 1.0131 |
| bulk-complex-p1 / lifecycle | 1849.834 | 1827.867 | 1.0042 | 0.9766–1.0355 | 1.0120 |
| bulk-complex-p1 / reused_buffers | 780.878 | 777.386 | 1.0060 | 1.0025–1.0107 | 1.0045 |
| bulk-f64-p0 / lifecycle | 703.883 | 713.213 | 1.0017 | 0.9334–1.0269 | 0.9869 |
| bulk-f64-p0 / reused_buffers | 238.295 | 238.040 | 1.0046 | 0.9598–1.0273 | 1.0011 |
| bulk-f64-p1 / lifecycle | 721.313 | 702.874 | 1.0087 | 0.9879–1.0372 | 1.0262 |
| bulk-f64-p1 / reused_buffers | 244.567 | 236.874 | 1.0661 | 0.9846–1.0945 | 1.0325 |
| small-complex-p0 / lifecycle | 7.243 | 6.479 | 1.1263 | 1.1105–1.1411 | 1.1180 |
| small-complex-p0 / reused_buffers | 7.307 | 5.014 | 1.1129 | 1.0831–1.4921 | 1.4573 |
| small-complex-p1 / lifecycle | 7.304 | 6.721 | 1.0811 | 1.0393–1.1854 | 1.0867 |
| small-complex-p1 / reused_buffers | 7.079 | 6.518 | 1.1162 | 1.0614–1.1441 | 1.0862 |
| small-f64-p0 / lifecycle | 4.181 | 3.263 | 1.2479 | 1.1999–1.2621 | 1.2813 |
| small-f64-p0 / reused_buffers | 2.759 | 2.212 | 1.2188 | 1.1603–1.3145 | 1.2473 |
| small-f64-p1 / lifecycle | 4.356 | 3.491 | 1.2192 | 1.1537–1.2742 | 1.2479 |
| small-f64-p1 / reused_buffers | 4.232 | 2.398 | 1.2277 | 1.1718–1.7732 | 1.7646 |
| tiny-complex-p0 / lifecycle | 1.915 | 1.480 | 1.4233 | 1.1634–1.4845 | 1.2939 |
| tiny-complex-p0 / reused_buffers | 0.910 | 0.630 | 1.4232 | 1.4094–1.5165 | 1.4442 |
| tiny-complex-p1 / lifecycle | 2.089 | 1.330 | 1.4297 | 1.4075–1.4678 | 1.5711 |
| tiny-complex-p1 / reused_buffers | 0.945 | 0.657 | 1.4006 | 1.3090–1.5553 | 1.4380 |
| tiny-f64-p0 / lifecycle | 1.767 | 1.182 | 1.4843 | 1.3927–1.5852 | 1.4957 |
| tiny-f64-p0 / reused_buffers | 0.866 | 0.980 | 1.4646 | 1.3171–1.5089 | 0.8832 |
| tiny-f64-p1 / lifecycle | 2.649 | 1.987 | 1.5096 | 1.4668–1.5450 | 1.3331 |
| tiny-f64-p1 / reused_buffers | 1.514 | 1.051 | 1.4360 | 1.4281–1.4788 | 1.4405 |

Tiny lifecycle paired ratios are **1.4233–1.5096**, or **566–795 ns** overhead;
reuse ratios are **1.4006–1.4646**, or **265–454 ns** overhead. Small lifecycle
ratios are **1.0811–1.2479**, or **555–938 ns** overhead; reuse is
**1.1129–1.2277**, or **472–705 ns** overhead. No absolute tiny-call budget has
been accepted. These unfavorable observations remain in the record.

Bulk lifecycle paired ratios are **1.0017–1.0164**, and reuse ratios are
**0.9876–1.0661**; their within-run interval upper bounds reach 1.0685 and
1.0945 respectively. This does not establish the controlled-host bulk budget.
Tiny real contiguous reuse illustrates the instability: its paired median is
1.4646 but its separate-median ratio is 0.8832. Small real padded reuse has an
interval reaching 1.7732. Neither statistic may be selected to claim parity or
speedup. No sample was removed.

## Diagnostic scopes and remaining limits

The diagnostic ranges below span the four scalar/layout cases within each size.
They time a selected packing/preflight or CBLAS call while executing the full
schedule; they exclude FFI. Timer/context overhead matters for tiny inputs.

| Size | First pack | Second regroup | First BLAS | Second BLAS |
| --- | ---: | ---: | ---: | ---: |
| tiny | 1.4394–1.7761 | 1.7437–1.8708 | 1.0273–1.1035 | 1.0256–1.1064 |
| small | 1.2691–1.7976 | 1.5131–1.6810 | 0.9720–1.0273 | 1.0088–1.0869 |
| bulk | 1.0457–1.1360 | 0.9999–1.0717 | 0.9646–1.0180 | 0.9532–1.0110 |

Second-regroup paired overhead is **49–67 ns** for tiny, **81–116 ns** for small,
and **−1–1,477 ns** for bulk (rounded). Small real first-pack ratios are
1.7595–1.7976; bulk real contiguous first pack is 1.1360 with interval
1.1239–1.1427. These remain slow-path observations, not attribution to a specific
check, FFI call or allocation. Scope medians cannot be subtracted to isolate
such costs; both paths use the same BLAS archive but their contexts can differ.

All **72 final calibration pairs** reached 5 ms on both sides, with a minimum
final batch of 5,042,811 ns. Subsequent measurements include **52 batches below
5 ms**: 15 lifecycle, eight reuse, 18 first-pack, ten second-regroup and one
first-BLAS; the minimum is 3,020,120 ns. No selective recalibration was applied.

Peak arena data is 2,825,248 bytes and peak arena metadata is 280 bytes. Generated
and C rows agree on every output/cost counter and finish with zero live arena
bytes. Every timed process reports **148,360 KiB** RSS. Linux launcher high-water
inheritance prevents interpreting that value as isolated executable heap.
Arena counters exclude Lean objects, allocator internals and BLAS private
workspace/packing; zero timed arena allocation is not zero total allocation.
The separate [stock runtime calibration](../../../stock_allocation_capabilities/results/2026-11-01-linux/RESULTS.md)
identifies some unsupported observation channels but does not fill these gaps.

A dedicated controlled host is unavailable and its gate is **not waived**.
Controlled repeatability, a predeclared tiny-call budget, unresolved overhead,
full allocation/backend-workspace attribution and representative workload
coverage remain. This record does not close #69/#183/#222 or historical Stage 1.
