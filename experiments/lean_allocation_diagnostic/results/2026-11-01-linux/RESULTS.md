# Linux private Lean allocator calibration

This independently downloaded record comes from the
[PR CI run](https://github.com/MGYamada/Vastitas/actions/runs/41279408438),
[Linux numerical job](https://github.com/MGYamada/Vastitas/actions/runs/41279408438/job/124768174689),
artifact `13072364021` (`lean-allocation-diagnostic-ubuntu-latest-pull_request`).
It measures the clean GitHub test merge
`5425c1ad3510fb708792d04abbe2ceba4b55efec`, with parents `a731c53` and feature head
`54531c11b2843a0d3d7565b71e7463e4387b8c03`. The published commit metadata and local
Git independently agree on tree `bb9cbb597c0bf86fdf078936cfc9f005c2f2bdd4`, identical
to that feature head. All 18 retained source snapshots match it exactly.
The later publication and final merge are separate revisions.

[evidence.zip](evidence.zip) is the original artifact ZIP, unchanged: 118 members,
8,869,546 bytes, SHA-256
`d878ea333a7114e58e099c33c639d86880c3ec1127a6bff8437f06b773a5c5a2`.
Its digest agrees with the Actions artifact metadata. It retains 33 commands
(including the pinned source download), raw/parsed streams, emitted C, binaries,
linker maps, all three runtime archives and the complete mimalloc source archive.
All installed toolchain fingerprints remained unchanged across the measurement.

The host was x86-64 Linux 7.0.0-1017-azure with glibc 2.43, GCC 15.2.0 for the
observer/Lean C driver and Clang 21.1.8 with libc++ for the private allocator
object. Lean was 4.35.0. The CPU model was not captured. Execution explicitly used
`LEAN_NUM_THREADS=0` and `LEAN_MAIN_USE_THREAD=1`: a single probe mutator on the
entry thread while the initialization thread waits. This shared CI runner is not
a controlled timing host; the calibration samples no operation timings.

The independent verifier passes all nine processes / 162 snapshots. Both private
archives preserve **34** original runtime objects and replace only
`mimalloc.cpp.o`. Their build commands differ only in the statistics level and
output paths. The stock runtime is retained without rebuild.

| Workload | Held / transient objects | Object/request / usable bytes | Stock/rebuilt-zero transient count | Diagnostic transient count |
| --- | ---: | ---: | ---: | ---: |
| Constructor | 1,024 / 10,000 | 40 / 40 | 0 (unsupported signal) | 10,000 |
| ByteArray | 13 / 257 | 1,025 / 1,280 | 0 (unsupported signal) | 257 |
| Huge ByteArray | 8 / 128 | 2,097,176 / 2,359,296 | 128 | 128 |
| Closure | 19 / 199 | 32 / 32 | 0 (unsupported signal) | 199 |
| Array | 17 / 263 | 824 / 896 | 0 (unsupported signal) | 263 |

Every known held pointer and its exact usable bytes appear in the main-heap
visitor and disappear on release. Diagnostic binned current-byte deltas return
to baseline after release/churn; repeated empty observations create no signal.
The final diagnostic normal totals are 11,792 allocations / 1,044,416 binned
bytes; the huge totals are 136 / 320,864,256. Requested-byte total/current are
955,406 and do not decrease: huge requests are omitted and the tested normal
releases are not subtracted. Stock/rebuilt-zero huge `current` remains cumulative,
whereas the diagnostic returns to baseline. Neither unsupported zero counters
nor cumulative current fields establish zero allocation, retention or a leak.

The visitor baseline is 2,985 objects / 124,728 usable bytes while diagnostic
normal counters begin at zero. The entry-thread query does not merge the waiting
initialization thread's counters. This record calibrates subsequent known
changes; startup and general simultaneous peaks remain unmeasured. The reported
observer objects total 2,591,360 bytes, excluding code/strings/alignment/stack and
reporting. Every process returns checksum 112,188.

The [macOS record](../2026-11-01-macos/RESULTS.md) has the same tested object
layouts, counts and release behavior under its separately recorded compiler and
host. This agreement is not a platform-wide theorem or a cross-host speedup.

```sh
python3 experiments/lean_allocation_diagnostic/verify.py \
  experiments/lean_allocation_diagnostic/results/2026-11-01-linux/evidence.zip
python3 -m unittest discover -s experiments/lean_allocation_diagnostic -p 'test_*.py'
```

All 15 focused archive/counter/provenance tests pass with both retained records.
General Lean/system/GMP/backend allocation, real source/FFI composition, meaningful
peak memory, native refinement and Fast like C acceptance remain outside this
calibration. No Stage 1 issue is closed by these results.
