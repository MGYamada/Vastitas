# macOS source block lifetimes: complete standard profile

This record measures clean `8212d7d0a6720e37913b6d44d5932e8ff263ead8` on
macOS 27.2 arm64. Source-cost schema 4 connects the actual checked two-edge
contraction source to the calibrated lifetime runtime across both backends.
It contains no operation timings or controlled-host acceptance claim.

The [complete compact record](evidence.zip) and
[manifest with full replay summary](artifact-manifest.json) preserve:

- All 12 tiny/small/bulk real/complex cases with/without padding, eight
  backend/runtime configurations and batches 1, 2 and 17.
- 96 canonical public check/build/executions using stock libraries; 1,152 normal
  observations, 96 failure cleanups and 18,048 actual CBLAS calls.
- 12,480 calling-thread statistics snapshots and 1,560 before/after lifetime
  boundary pairs, each checked against an independent main-heap visitor.
- 70 actual source packing contracts, checked by 280 additional plain/sanitized
  stock/diagnostic footprint executions.
- Both complete nested allocator calibrations, the backend calibration, exact
  returned source and raw commands, linker maps and all object/archive receipts.
  All 86 source snapshots match the measured Git commit.

The archive has 12,841 members and 67,100,281 bytes. Its SHA-256 is
`691c60a56af4ce3af872b292833ac281b9f1ff982fd4170dd022c0d5f71ee0f5`.
The exporter independently replays the build directory and compact archive and
requires identical summaries. Executable files and Lake caches are excluded;
their exact hashes and sizes remain in the record. No archived code is executed.
The complete source replay/mutation suite passes against this ZIP: 90 tests,
no skips. Publication fixes a mutation-test helper to inspect the same case it
modifies, rather than independently selecting two files from an unordered set.
That correction changes test selection, not the measurement or native code.

## Observed logical-block costs

Within the private lifetime runtime, all cases and both backends agree on the
following run-scope costs. Independent calling-thread statistics reconcile their
allocation counts, usable-byte traffic and changes in live bytes.

| Run scope | Allocations / frees | Requested / acquired / released bytes | Peak usable bytes above entry |
| --- | --- | --- | --- |
| Generated lifecycle, 1 operation | 5 / 5 | 104 / 104 / 104 | 72 |
| Generated lifecycle, 2 operations | 7 / 7 | 144 / 144 / 144 | 72 |
| Generated lifecycle, 17 operations | 37 / 37 | 744 / 744 / 744 | 72 |
| Generated caller-buffer reuse, any batch | 3 / 3 | 64 / 64 / 64 | 48 |
| Matched C, either scope/any batch | 0 / 0 | 0 / 0 / 0 | 0 |
| Checked generated failure | 7 / 7 | 180 / 184 / 184 | 136 |

The failure's two actual error payload objects have 92 requested / 96 usable
bytes, separately from the selected error-result object. The channels overlap:
do not add selected-site, statistics and lifetime counts. The C comparison
remains Lean-hosted; cold generated work and initialization precede its run
scope. Zero run-scope counts are not zero startup cost or standalone-C evidence.

Pre-cold state retains 11,130–11,132 allocations and 2,986 live blocks,
124,768 or 124,776 live usable bytes, and a global peak of 125,040 or 125,048
bytes. Initialization and command-argument traffic remain visible. Setup can
release a preexisting argument while still allocating; the signed live-byte
change is not itself an allocation count. Interval peaks reveal transient run
storage even when entry and exit live bytes agree and startup had a higher peak.

The [separate complete streaming record](../2026-11-02-macos-lifetimes-streaming/RESULTS.md)
uses the same clean revision and identical 86 source inputs, with 128 / 256 MiB
outputs and batches 1 and 2. It is additional cost coverage, not a timing result
or evidence of a particular cache/DRAM bottleneck.

The lifetime observer adds 4,194,417 declared static bytes and 1,208 bytes of
phase storage, separately from the existing 43,732-byte statistics observer.
Native arena costs and backend pool capacity are separate channels; independent
peaks cannot be summed as a simultaneous whole-process peak. Physical allocator
backing/RSS, libc/GMP and other allocator traffic, reporting, process teardown,
stock timing, full cost attribution and Fast like C acceptance remain open.
