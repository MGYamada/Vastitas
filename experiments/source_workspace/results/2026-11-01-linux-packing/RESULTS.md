# Checked source GEMM packing costs — Linux

Full schema-3 record from clean
`6abeee14b708e9bc1752c420949043971dc48a28`, independently downloaded and replayed
after the successful hosted run. This is cost evidence, not timing acceptance or
native refinement.

| Provenance | Value |
| --- | --- |
| Host | Shared GitHub Linux x86_64 runner, glibc 2.43; `/usr/bin/cc`; no controlled-host claim |
| Workflow | [Push run 41297813661](https://github.com/MGYamada/Vastitas/actions/runs/41297813661), [successful Linux job 124822271001](https://github.com/MGYamada/Vastitas/actions/runs/41297813661/job/124822271001) |
| Lean | Installed 4.35.0 plus private rebuilt-zero / `MI_STAT=2` runtime archives |
| Nested calibrations | Both measure clean `6abeee14b708e9bc1752c420949043971dc48a28`; complete Lean and backend records retained inside this archive |
| Backend | Schema-2 packing calibration; pinned sequential LP64 OpenBLAS 0.3.34, explicit HASWELL target, `NO_WARMUP` |
| Source inputs | All 78 repository snapshots match their Git blobs and the same-revision macOS record |
| Source commands | 1,931, including kernel input hashes, actual output streams and source packing calibrations |
| Downloaded Actions artifact | `13080569980`, 66,842,759 bytes; SHA-256 `322d74d245b070b307e673158ca8368d7f5c3f82889e9415e5e444ebe7367f59` |
| Retained inner archive | [evidence.zip](evidence.zip), 10,900 members, 72,029,976 bytes |
| Inner SHA-256 | `8f188837886a60a2ba20796f04c8c233108173f5d35816b0cdf9097cdd1eb1e1` |
| Export manifest | [artifact-manifest.json](artifact-manifest.json) |

The downloaded outer ZIP matches GitHub's artifact digest. It contains only this
byte-identical inner archive and manifest. Canonical public executables use stock
Lean and stock BLAS; only private observation executables select the calibrated
archives. Linker maps and independent source/archive/toolchain fingerprints bind
those variants. Production compiler, protocol and runtime behavior is unchanged.

## Source and packing observations

All twelve tiny/small/bulk, real/complex, padded/unpadded cases cross three Lean
runtimes with two backends: **72 canonical public check/build/executions, 864
normal observations and 72 checked failure cleanups**. Every one of the **13,536
actual CBLAS calls** retains its matrix addresses, arguments and event interval.
Each diagnostic route must match the actual call; each copy must remain within
its source rectangle and active pool loan.

The source executions exercise **66 distinct packing kernel/shape/stride
contracts**, all outside the nested backend calibration's 133-contract fixture
set. Every source contract is independently executed against both exact backend
archives on plain and ASan/UBSan harnesses: **264 additional footprint
executions**. The archive retains complete compile/link/execution receipts,
binary fingerprints, input/padding checks and output footprints.

Each operation contains two GEMMs. Padded/unpadded variants have the following
observed logical payloads and copy-call counts:

| Case | First GEMM A / B bytes | Second GEMM A / B bytes | Copy calls, first / second | Explicit arena packing bytes |
| --- | ---: | ---: | ---: | ---: |
| Tiny F64 | 192 / 120 | 320 / 192 | 2 / 2 | 512 |
| Tiny complex | 384 / 240 | 640 / 384 | 4 / 2 | 1,024 |
| Small F64 | 4,760 / 1,496 | 3,080 / 520 | 3 / 3 | 7,840 |
| Small complex | 9,520 / 2,992 | 6,160 / 1,040 | 5 / 4 | 15,680 |
| Bulk F64 | 245,760 / 15,360 | 294,912 / 14,336 | 4 / 6 | 540,672 |
| Bulk complex | 491,520 / 30,720 | 589,824 / 28,672 | 12 / 16 | 1,081,344 |

Logical payload agrees with the [macOS record](../2026-11-01-macos-packing/RESULTS.md)
for these cases, while the actual packing call counts differ. Each repeated panel
is counted. Generated/C costs agree across lifecycle/reuse, repetitions 1/2/17
and all three Lean variants. All source routes observed here use the packed path;
enabled shortcut internals remain unmeasured, and stock payload observations stay
null. Logical copies and explicit arena packing do not measure physical traffic,
cache behavior or elapsed time.

## Other cost channels and limits

The 936 processes retain **9,360 allocator snapshots**. All 312 calibrated
`MI_STAT=2` processes have agreeing immediate empty repeats and no unattributed
normal allocation in their recorded phases. Lifecycle run counts remain `3N+3`
normal objects / `56N+64` binned bytes; prepared/reuse runs retain three fixed
wrapper/control objects / 64 bytes per batch. Matched C has zero observed normal
allocations within its Lean-hosted run scope. Failure includes the actual
two-object / 96-byte error payload. These channels overlap with selected-site
counts and must not be added together; stock counts remain unavailable.

The 468 backend-diagnostic processes observe 6,768 pool borrows and matching
returns. Each retains one **128 MiB** virtual mapping after cold work and releases
it at explicit shutdown. The named static pool declarations total **4,484 bytes**.
Observers remain separately charged: source-call bridge 30,740 bytes, workspace
163,869, packing 1,339,420 and allocator 43,732. These declared sizes exclude
alignment, code, strings, stack and reporting costs; virtual backing is not RSS
or whole-process peak memory.

All 64 source tests passed in the measured Linux job. Independent archive replay
matches the manifest, and all 78 source inputs were checked against actual Git
blobs without executing archived code. The nested backend's 26 and Lean
calibration's 18 repository inputs also match their measured Git revision.
All 65 publication tests passed with both source-record environment variables
selecting this Linux ZIP, including independent replay of both retained exports
without relabeling either measured revision. Dependency boundaries, whitespace
and 171 local Markdown targets passed. Large
source executables and Lake caches are omitted, with fingerprints preserved.
Hashes establish integrity/correspondence, not authenticity or native refinement.

Clocks are disabled. Waiting-thread startup, other allocators and backend files,
general heap/peaks, shortcut payload, representative memory-bound workloads,
unresolved tiny-call overhead and the predeclared budget/controlled-host
performance gates remain open. These records do not establish Fast like C.
