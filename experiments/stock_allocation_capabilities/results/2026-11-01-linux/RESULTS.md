# Stock Lean allocation capability record — Linux, 2026-11-01

The unchanged installed Linux Lean runtime exhibits the same tested capability
limits as the [separate macOS record](../2026-11-01-macos/RESULTS.md). This is a
three-process allocator observation calibration, with no operation timings,
production-runtime rebuild/hooks or whole-process allocation claim.

The measured source is clean
`8e548d3188d82d4754fb052cbfe81d3f8e362b24`, the integrated PR #355 head, not the
earlier macOS feature revision or this later publication commit. The
[workflow run](https://github.com/MGYamada/Vastitas/actions/runs/41263966381)
and [Linux job](https://github.com/MGYamada/Vastitas/actions/runs/41263966381/job/124722965839)
completed the stock calibration and its independent verifier. The downloaded
artifact `13066351712` is retained unchanged as [evidence.zip](evidence.zip):
1,316,957 bytes, 57 members, SHA-256
`49fa4f3365657ea9f881768f03c8648df07a6128a73198c1689ef680d5b1c7de`.
The local verifier also accepted that exact ZIP after download, independent of
the workflow's recorded success. [artifact-manifest.json](artifact-manifest.json)
retains its service provenance; [summary.json](summary.json) indexes the results.

The host was x86-64 Linux 7.0.0-1017-azure with glibc 2.43 and GCC 15.2.0.
Lean was unchanged 4.35.0 Release (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`),
mimalloc 3.4.5 with statistics schema 5. All 11 repository and nine installed
toolchain inputs have stable before/after fingerprints. The observer links no
OpenBLAS library and uses one probe mutator with `LEAN_NUM_THREADS=0`.

All three fresh processes verified eight snapshots each. Baseline main-heap
occupancy was 2,985 blocks / 124,728 allocator block bytes. Holding 1,024 small
constructors added exactly 40,960 bytes and all known pointers; holding eight
2 MiB ByteArrays added exactly 18,874,368 bytes and all eight pointers. Each
release returned to the exact baseline. Payload/header/block sizes remain
distinct, as in the macOS report.

The 10,000 transient small allocations produce a normal-count delta of zero:
that channel is unsupported for this churn, not evidence of zero allocations.
The 128 transient large allocations produce a huge-count delta of 128, calibrated
only for this tested path. Huge `current`/`peak` remain cumulative after the
known objects disappear; they are not logical live bytes or measured peak
retention. The observer separately charges its 1,220,328 snapshot-buffer bytes
and 16,512 known-object table bytes. Backing/process diagnostics are non-additive.

Recheck the immutable record without rebuilding or executing the probe:

```sh
python3 experiments/stock_allocation_capabilities/verify.py \
  experiments/stock_allocation_capabilities/results/2026-11-01-linux/evidence.zip
```

The two records support only the stated known-object/size/path calibration.
They do not measure general Lean allocation churn, other heaps/allocators,
between-snapshot peaks or OpenBLAS workspace/backing. They add no native-refinement
proof or controlled-host Fast like C acceptance. The original macOS archive and
its source revision remain unchanged.
