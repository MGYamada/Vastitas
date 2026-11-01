# Private Lean block lifetime calibration

This experiment observes successful mimalloc block acquisitions and logical
releases across threads, including Lean initialization. A fixed table tracks
allocation provenance, usable bytes and the maximum simultaneous live usable
bytes between explicit observation boundaries. It complements the existing
calling-thread `MI_STAT=2` calibration; those older counters do not establish
startup accounting or a combined normal/huge live peak.

The profile is pinned to Lean 4.35.0 and mimalloc 3.4.5. It replaces exactly
`mimalloc.cpp.o` in a **private copy** of `libleanrt.a`, links the observer as a
separate object and preserves every other runtime member byte for byte. The
installed runtime and ordinary compiler remain unchanged. The private profile
sets `MI_STAT=2`, `MI_PADDING=0`, `MI_MAX_ALIGN_SIZE=8` and `MI_SECURE=0`.

The retained [macOS record](results/2026-11-02-macos/RESULTS.md) measures clean
`a6ff4d0`; the [Linux record](results/2026-11-02-linux/RESULTS.md) measures its
identical-tree CI test merge `e732f25`. Each has seven normal executions, two
expected capacity failures, 54 Lean and 44 native snapshots, and 34 unchanged
runtime objects. The verifier and 26 observation/provenance regressions accept
both. No timing claim follows.

```sh
python3 experiments/lean_allocation_lifetimes/run.py --out /tmp/lifetime-record
python3 experiments/lean_allocation_lifetimes/verify.py /tmp/lifetime-record
VASTITAS_HEAP_LIFETIME_RECORD=/tmp/lifetime-record \
  python3 -m unittest discover -s experiments/lean_allocation_lifetimes -p 'test_*.py'
```

Use a fresh output directory outside the checkout. Linux needs Clang with
libc++/libc++abi headers and libraries; macOS uses the host C compiler through
`LEAN_CC`. `--mimalloc-archive` accepts an existing release archive only when its
SHA-256 matches the pinned release. Loader/compiler injection options are
rejected; inherited mimalloc and sanitizer overrides are removed and recorded.

## Calibration and record audit

Three fresh Lean processes run the existing constructor, byte-array, large
byte-array, closure and array workloads. Each snapshot brackets the independent
heap visitor and allocator-statistics observation with two lifetime reads. They
must agree exactly, and the visitor must report the same live block count and
usable bytes. Known hold, release and churn phases check counts, request traffic,
usable traffic and interval peaks independently. Startup traffic is retained,
not reset or assumed identical across fresh processes.

Three fresh native processes additionally exercise mixed small/large blocks,
in-place and moving reallocations, alignment, foreign-thread free, bulk heap
destruction and heap deletion with surviving allocations. Eight workers perform
160,000 known allocation/free pairs between synchronized boundaries. Their own
`mi_usable_size` sums and maximum simultaneously held pairs bound the observed
concurrent peak. These are finite calibration cases, not coverage of every
mimalloc API or concurrent heap-destruction pattern.

A separate native run applies ASan/UBSan to the **observer and probe**, with the
same unsanitized upstream allocator object. LeakSanitizer is disabled. Ordinary
and sanitized capacity runs must terminate with exit 90 and the exact observer
audit diagnostic. A full table, untracked free, inconsistent usable size or
counter overflow fails instead of returning a truncated observation.

The record retains raw stdout/stderr, parsed observations, commands and explicit
environment overrides, repository inputs, emitted C, object files, executables,
link maps, original runtime archive and toolchain fingerprints. It also retains
the checksum-pinned mimalloc archive and the complete modified source tree.
Offline verification reconstructs the four modified files from the original
archive and rejects changes elsewhere. It checks the exact rendered Lean probe,
reviewed native sources, runtime-member replacement, selected link origins,
compiler flags, process coverage, all observation equations and failure controls.
It never executes code from the record. Hashes and logs preserve an inspectable
experiment; they are not independent attestation that an adversarial producer
ran the compiler or executable it reports.

## Cost meaning and boundaries

`allocated_requests` counts requests at the low-level allocation hook, including
internal alignment over-allocation when present. It is not live payload size or
the sum of all public reallocation requests. Successful same-block resizing has
separate `resizes` and `resize_requests` counters; it does not invent an allocation
or release. `allocated_usable` and `freed_usable` count actual block capacities.
Their difference is `live_usable`. `peak_usable` covers the observed process
history and `interval_peak_usable` covers an explicit interval, including its
starting live set. The maximum is updated in the same lock as the lifetime table;
it is not a sum of separately sampled size-class peaks. A checkpoint returns the
completed interval and begins the next interval in one critical section, so
callbacks cannot fall into a gap between the snapshot and interval reset.

The observer has 131,072 entries and reports 4,194,417 bytes of static table,
counters and lock storage on the supported 64-bit ABI. Alignment padding, code
and stack are separate. Observation uses no dynamic allocation. Heap deletion
rehomes surviving block provenance; bulk destruction records logical releases.
The release hook precedes completion of allocator bookkeeping. It does not mean
physical pages have already returned to the OS.

These are private instrumented-runtime counts, **not** stock execution timings,
OS backing/RSS, arbitrary libc/GMP allocation accounting, full process-exit
accounting, native refinement or completion of the Fast like C gate. The runtime
can retain genuine allocator metadata after a fixture; independent heap visiting
checks that state instead of labeling it a leak or subtracting it away. Public
`.vast` source composition, remaining native/backend channels and controlled-host
performance acceptance are separate work.
