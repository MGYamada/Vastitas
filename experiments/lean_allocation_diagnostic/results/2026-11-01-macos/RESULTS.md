# macOS private Lean allocator calibration

Measured clean revision: `54531c11b2843a0d3d7565b71e7463e4387b8c03`.
The later publication/merge revision does not change that measurement.

[evidence.zip](evidence.zip) has 116 members, 6,049,760 bytes and SHA-256
`a7774c7130dc59491498aa9add1e6162f40c57ab84bf1f4aa7a997355efc0232`.
All 18 repository input snapshots were independently matched to the measured
Git revision. The archive retains 32 commands, raw and parsed observations,
installed headers, emitted C, binaries, linker maps, the complete pinned mimalloc
source archive and all three runtime archives. Installed inputs were hashed
before and after and remained unchanged.

The host was macOS 27.2 arm64 with Apple Clang 21.0.0 and Lean 4.35.0. The
execution overrides were `LEAN_NUM_THREADS=0`, `LEAN_MAIN_USE_THREAD=1` and the
recorded C compiler. This is a single probe mutator on Lean's ordinary entry
thread while the initialization thread waits; it is not a one-thread process.
No operation timings, OpenBLAS or controlled-host acceptance are measured.

All nine processes and 162 snapshots pass the independent verifier. In both
private runtimes, only `mimalloc.cpp.o` changes; the other **34** archive members
remain byte-identical in their original order. The two rebuilds use the same
compiler and flags apart from `MI_STAT=0/2`; the stock archive is retained exactly.
The zero-statistics rebuild is not claimed identical to the installed object.

| Workload | Held objects | Transient objects | Object/request bytes | Usable block bytes | Stock/rebuilt-zero transient count | Diagnostic transient count |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Constructor | 1,024 | 10,000 | 40 | 40 | 0 (unsupported signal) | 10,000 |
| ByteArray | 13 | 257 | 1,025 | 1,280 | 0 (unsupported signal) | 257 |
| Huge ByteArray | 8 | 128 | 2,097,176 | 2,359,296 | 128 | 128 |
| Closure | 19 | 199 | 32 | 32 | 0 (unsupported signal) | 199 |
| Array | 17 | 263 | 824 | 896 | 0 (unsupported signal) | 263 |

For each workload, the visitor sees every known held address and exactly the
expected additional count/usable bytes; both return to baseline after release
and after transient work. Diagnostic normal/huge current-byte deltas also return
to baseline. Empty repeated observations add no allocation signal.

The diagnostic final normal totals are 11,792 allocations and 1,044,416 binned
bytes. Its requested-byte total/current are both 955,406: this channel counts
normal requests, omits the huge requests and never decrements on the tested
releases. The 136 huge allocations account for 320,864,256 cumulative binned
bytes. Huge `current` stays at that cumulative amount in stock/rebuilt-zero and
returns to baseline in the diagnostic. The stock value is not a leak or live-size
measurement.

The baseline visitor sees 2,985 objects / 124,728 usable bytes; baseline diagnostic
normal counters are zero because the waiting initialization thread's counters
have not been merged by the entry thread's query. This record calibrates the
subsequent known changes, not startup or a global live-heap total. Peak and
allocator backing fields remain raw diagnostics, not additive cost channels or
a proof of general peak coverage.

Reported observer storage is 2,574,728 snapshot bytes, 16,384 pointer-table bytes,
240 workload-table bytes and an 8-byte checksum. Code, strings, alignment, stack
and reporting are excluded. The retained checksums are 112,188 in every process.

Verification:

```sh
python3 experiments/lean_allocation_diagnostic/verify.py \
  experiments/lean_allocation_diagnostic/results/2026-11-01-macos/evidence.zip
python3 -m unittest discover -s experiments/lean_allocation_diagnostic -p 'test_*.py'
```

The focused suite passes all 15 archive/counter/provenance mutation tests. These
are diagnostic calibration results, not stock-production counts, actual Vastitas
source allocation coverage, general peak measurements, native refinement or
Fast like C acceptance. The next connection is to the independently checked
source/FFI observation, with those boundaries kept explicit.
