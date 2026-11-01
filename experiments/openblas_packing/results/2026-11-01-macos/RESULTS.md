# macOS actual GEMM packing calibration

Measured clean commit `8422c35dbe90c383451b4065a8b584bb4661e5cf` on
2026-11-01. The full [evidence archive](evidence.zip) and
[manifest](artifact-manifest.json) retain all 5,602 members. The ZIP is
5,744,369 bytes, SHA-256
`3466111f9fed4822a8bcc1de63d10d39729aa34100ff2c5961eb8e758bb17488`.
All 26 repository input hashes match the actual Git blobs at that revision.
Later publication/verifier changes do not relabel this measurement.
This initial schema-1 record uses the broad direct-kernel grid. Its 136 distinct
observed `(kernel,m,n,lda)` contracts include blocks up to 512 and strides outside
that grid. The current schema-2 runner adds direct checks of every actual contract;
those additional checks are not retroactively claimed by this record.

The machine uses macOS 27.2 / arm64 and Apple Clang 21. The paired OpenBLAS
0.3.34 backend is sequential LP64 VORTEXM4 with upstream-selected `NO_WARMUP`.
No operation clocks or controlled-host timings are collected. This calibration
does not include generated Vastitas source execution.

## Checks and observations

- All 1,828 executions / 914 stock-diagnostic pairs passed: 457 cases, two fresh
  processes per variant. Complete output/input/padding checks agree with the
  independent integral reference, including complex N/T/C and accumulation.
- Each of four direct-kernel binaries (stock/diagnostic, plain/sanitized harness)
  passed 6,348 coordinate/guard cases and checked 37,307,664 output words. The
  six actual copy symbols use D unroll 8/4 and Z unroll 4/4. Upstream objects
  themselves are not sanitizer-instrumented; these are finite calibration cases.
- Exactly 23 observer/CBLAS/GEMM-driver objects differ. All 535 kernel objects,
  including compute, copy and shortcut kernels, retain their stock hashes.
- Diagnostic records contain 972 actual CBLAS routes: 780 packed GEMM, 144 empty,
  and 48 GEMV. The actual adapter skips its empty operations before CBLAS.
  No small-matrix route was observed on this configuration; that is not proof
  that all backends or workloads lack one.
- There are 308,750 actual copy invocations, with 103,993,280 left-input and
  397,384,256 right-input logical packed payload bytes across the diagnostic
  executions. Every span passes input-rectangle, calibrated-kernel, route and
  active-pool checks. Repeated input coverage remains charged repeatedly.
- For `(m,n,k)=(2,50000,7)`, N/N overwrite packs the 112-byte real left input
  13 times (1,456 bytes) and the 224-byte complex left input 25 times (5,600
  bytes). Right-input payload is 2,800,000 / 5,600,000 bytes respectively.
  Operand size alone therefore misses repacking in this actual driver.
- The named declared pool metadata totals 4,508 bytes: a 3,200-byte memory table,
  a 1,200-byte release table, a 64-byte allocation mutex, three 8-byte
  pointers/address fields and five 4-byte flags/counters. This excludes other
  backend data, linker padding, read-only tables, stack and libc metadata.
- The packing observer declares 1,339,420 mutable bytes separately from the
  workspace observer and workload. This diagnostic storage is not a stock cost.

The 48 GEMV routes retain **unavailable** packing payload, not a zero-storage
claim. Logical payload is not hardware traffic, retained pool capacity, requested
backing, RSS or a general peak. Do not sum overlapping channels into total heap
cost. The full [experiment contract](../../README.md) lists exclusions and exact
reproduction commands.

The directory and exported ZIP both passed independent replay. All 23 unit,
mutation and full-record tests passed using this record; local dependency-boundary
and documentation-link checks passed. Hosted Linux/macOS validation remains
recorded on [PR #369](https://github.com/MGYamada/Vastitas/pull/369).
Generated-source composition, shortcut internals, complete cost/peak attribution
and the existing Fast like C performance gates remain open.
