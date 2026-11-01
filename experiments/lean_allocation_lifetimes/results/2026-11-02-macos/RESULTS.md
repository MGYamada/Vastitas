# macOS private block lifetime calibration

Measured clean revision: `a6ff4d07180a1652648abaacb7c6bf7557b733b0`.
The later publication/merge revision is separate. All **27** repository input
snapshots were independently matched to that Git revision before publication.

[evidence.zip](evidence.zip) contains 495 members and 5,300,272 bytes, SHA-256
`5766f9a86a0ee1e618358bc3d1ad293548162b1a98e134a876721398fcf1c4ef`.
It retains the complete pinned allocator archive and reconstructed source tree,
original/private runtime archives, observer objects, emitted C, executables,
link maps, all commands, raw outputs and parsed observations. Installed inputs
were fingerprinted before and after and remained unchanged.

The host was macOS 27.2 arm64, Apple Clang 21.0.0 and Lean 4.35.0. The exact
C++ driver name is preserved as `clang++`. Lean runs set `LEAN_NUM_THREADS=0`
and `LEAN_MAIN_USE_THREAD=1`: the entry-thread probe runs while the initialization
thread waits. This is not a one-thread process or a controlled timing host.

All **7** normal executions pass offline replay: three fresh public-Lean-API
fixtures, three fresh native fixtures and one ASan/UBSan observer/probe fixture.
They retain **54 Lean snapshots and 44 native snapshots**. Native and sanitized
capacity controls both return exactly exit 90 and the required audit diagnostic.
Only `mimalloc.cpp.o` changes in the private runtime; the other **34** members
remain byte-identical and in the same order. The observer is linked separately.

| Observation | Retained result |
| --- | ---: |
| Lean baseline live blocks / usable bytes, all three runs | 2,985 / 124,728 |
| Startup allocations, runs 1 / 2 / 3 | 11,106 / 11,105 / 11,105 |
| Startup allocation-hook requests, runs 1 / 2 / 3 | 249,275 / 249,251 / 249,251 bytes |
| Lean fixture maximum simultaneous usable bytes, all runs | 18,999,096 |
| Native held small + 4 MiB + 32 MiB usable-byte peak | 37,748,752 |
| Synchronized eight-worker allocations and frees, each native run | 160,000 / 160,000 |
| Native retained allocator metadata at the final boundary | 1 block / 320 usable bytes |
| Lifetime observer fixed storage | 4,194,417 bytes |

The independent heap visitor agrees with every Lean live-set observation and
each stable native fixture boundary. Known held, released and transient object
counts and byte traffic agree exactly. The startup differences are retained;
fresh processes are not assumed to allocate identically. The worker peaks vary
with scheduling (42,144 / 42,096 / 42,032 bytes; sanitized 42,056), within the
independently computed held-pair bounds. All workers restore their initial live
set. The final 320-byte metadata block is also independently visited, not
silently removed or labeled a leak.

```sh
python3 experiments/lean_allocation_lifetimes/verify.py \
  experiments/lean_allocation_lifetimes/results/2026-11-02-macos/evidence.zip
python3 -m unittest discover -s experiments/lean_allocation_lifetimes -p 'test_*.py'
```

The 26 observation/provenance regressions pass. ASan/UBSan cover the observer and
probe, not the upstream allocator object; LeakSanitizer is disabled. The older
calling-thread diagnostic retains its original meaning. This record calibrates
private logical block lifetimes and finite interval peaks, not public `.vast`
source composition, libc/GMP allocation, physical backing/RSS, stock-runtime
speed, native refinement or the Fast like C acceptance gate.
