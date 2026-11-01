# Stock Lean allocation capability record — 2026-11-01

This is a capability calibration of the unchanged installed Lean runtime, not
a Vastitas workload benchmark or total-allocation result. It measures clean
feature revision `8e516d500e234e6a61a0910fd915f862ea7e7773`, before the commit that
publishes this record. No Lean, compiler, storage runtime or OpenBLAS implementation
was rebuilt or instrumented. A separate observer executable was compiled.

The [evidence archive](evidence.zip) contains 57 files, 724,123 compressed bytes,
SHA-256 `eb8959816763b84328dd55ae69e1d487ed4fe6a4bd415d976febf4a7f038b2dd`.
It retains raw and parsed observations from three fresh processes, emitted Lean C,
objects and executable, source/header snapshots, compiler/linkage logs and the
complete hash inventory. Eleven repository inputs and nine installed toolchain
inputs have matching before/after fingerprints. Six installed headers are
retained; the Lean executable, Lean C driver and runtime archive are fingerprinted.
The compact [summary](summary.json) is a convenience index; the archive is the
independently verifiable record.

The host was macOS 27.2 arm64 with Apple clang 21.0.0. The installed toolchain was
Lean 4.35.0 Release, Lean commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, with mimalloc 3.4.5 and statistics
schema 5. The pinned MIT header and its license are included. The probe uses
`LEAN_NUM_THREADS=0` and no other mutator tasks; the heap visitor is not used as a
concurrent production observer. No OpenBLAS library is linked into the probe.

## Actual observations

All three processes produced the same known-object calibration and capability
classifications. Each contains eight snapshots: baseline, small held/released,
large held/released, small transient, large transient and a separate forced
collection. The baseline was 2,985 main-heap blocks / 124,728 allocator block bytes.

| Operation | Observed result | Permitted interpretation |
| --- | --- | --- |
| Hold 1,024 constructors with 32 scalar payload bytes | Every known pointer found; +1,024 blocks and +40,960 block bytes | Each tested 40-byte Lean object occupies a 40-byte allocator block on this host |
| Release those constructors | Known pointers disappear; live blocks/bytes return exactly to baseline | Tested release is visible at the sample |
| Hold eight 2 MiB ByteArrays | Every known pointer found; +8 blocks and +18,874,368 block bytes | Each object requests 2,097,176 bytes including its header; allocator block size is 2,359,296 bytes |
| Release the ByteArrays | Known pointers disappear; live blocks/bytes return exactly to baseline | Tested release is visible; the huge counter's unchanged `current` is not live bytes |
| Allocate/release 10,000 transient small objects | `malloc_normal_count` delta 0; final live snapshot is baseline | Stock counter is unsupported for this churn, not evidence of zero allocation |
| Allocate/release 128 transient large objects | `malloc_huge_count` delta 128; final live snapshot is baseline | Count calibrated only for this tested size/path; not a universal allocation counter |
| Huge-byte accounting after all large objects are released | `current` and `peak` remain 320,864,256 (136 × 2,359,296) | These fields are cumulative for this observed build/path, not live or peak retained memory |

The checksum is 78,664 in every process. The observer separately reports 1,220,328
static snapshot bytes and 16,512 known-object table bytes. Observation buffers/API
paths are warmed before baseline; visitor callbacks allocate nothing and printing
happens after the last snapshot. These observer costs are not claimed to disappear.
Allocator backing and process RSS/CPU-time diagnostics are retained separately,
without adding overlapping measures to logical object bytes.

The [pinned-source explanation](../../README.md#pinned-source-explanation) explains
the observed asymmetry: normal counters and free-side decrements are conditional,
while huge allocation accounting remains enabled. The fused small-object fast
path also prevents treating an exported malloc hook as complete coverage.
These observations concern this exact installed build; they do not identify all
allocator paths or establish a native-refinement theorem.

## Reproduction and validation

From the repository root:

```sh
python3 experiments/stock_allocation_capabilities/run.py \
  --out /tmp/vastitas-stock-capabilities-new --cc cc
python3 experiments/stock_allocation_capabilities/verify.py \
  experiments/stock_allocation_capabilities/results/2026-11-01-macos/evidence.zip
python3 -m unittest discover \
  -s experiments/stock_allocation_capabilities -p 'test_*.py'
```

The retained run compiled emitted C and the observer with `-O3 -Wall -Wextra
-Werror`, linked against the unchanged installed runtime, and passed independent
verification of all three processes / 24 snapshots. All 18 observation and
retained-record regression tests passed after archiving, with no skips. They
reject missing/repeated observations, incomplete release/pointer coverage, invalid
integer domains, unsupported claims, false classifications, raw/parsed drift,
changed fingerprints, inventory omissions and rehashed inconsistent observations.
Workflow YAML parsing, repository dependency boundaries and `git diff --check`
also passed. Linux execution remains a separate CI result, not this macOS record.

This does not complete #183/#222 or the historical Stage 1 performance gate.
No equivalent-C operation timing, between-snapshot peak, general Lean churn,
other allocator/heap or OpenBLAS workspace attribution is claimed. Those remaining
channels must be calibrated and reported separately. A diagnostic rebuilt
allocator may expose more events, but must not be labeled stock-runtime evidence.
