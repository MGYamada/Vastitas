# Checked source GEMM packing costs — macOS

Full schema-3 record from clean
`6abeee14b708e9bc1752c420949043971dc48a28`. It connects actual generated-source
CBLAS calls to calibrated packing, alongside the existing allocator and arena
channels. This is cost evidence, not timing acceptance or native refinement.

| Provenance | Value |
| --- | --- |
| Host | macOS 27.2, arm64; `/usr/bin/cc`; no isolated CPU or controlled-host claim |
| Lean | Installed 4.35.0 plus private rebuilt-zero / `MI_STAT=2` runtime archives |
| Lean calibration | Clean `54531c11b2843a0d3d7565b71e7463e4387b8c03`; complete calibration retained inside this archive |
| Backend calibration | Clean `db62d224837031f1a8b3e05e6ca4756325716a04`; schema 2, pinned sequential LP64 OpenBLAS 0.3.34, VORTEXM4, `NO_WARMUP` |
| Source inputs | All 78 repository snapshots independently matched to the measured Git revision |
| Source commands | 1,947, including kernel input hashes, actual output streams and source packing calibrations |
| Compact archive | [evidence.zip](evidence.zip), 10,922 members, 49,217,480 bytes |
| SHA-256 | `47e027b31d81070b89cb798f6ee5d803530f4cff1a3cb4219a20e22075f183d0` |
| Export manifest | [artifact-manifest.json](artifact-manifest.json) |

The reused calibrations keep their own measured revisions. Their exact archives,
headers, observer inputs and toolchain fingerprints are checked before use.
Canonical public executables use stock Lean and stock BLAS; only the private
observation executables select calibrated variants. No installed toolchain,
production compiler, public wire protocol or native runtime is modified.

## Actual source and packing coverage

All twelve tiny/small/bulk, real/complex, padded/unpadded cases cross three Lean
runtimes with two backends: **72 canonical public check/build/executions, 864
normal observations and 72 checked failure cleanups**. All **13,536 actual CBLAS
calls** retain exact shape, leading dimensions, transforms and coefficients.
Schema 3 additionally captures the actual three matrix addresses at each wrapper
call. Each diagnostic route must match those addresses and the complete event
interval. Cross-process comparisons use logical costs, not address equality.

The source executions exercise **70 distinct packing kernel/shape/stride
contracts**, all outside the backend calibration's separate 136-contract fixture
set. Each source contract is therefore executed independently against both exact
stock/diagnostic archives, with plain and ASan/UBSan harnesses: **280 additional
footprint executions**. Compile/link arguments, source/archive hashes, binary
fingerprints, input/padding preservation and complete output footprints are
retained and replayed. These checks do not infer coverage from similar dimensions
or from the older grid alone.

Each contraction-tree operation has two GEMMs. For both padded and unpadded
variants, the observed logical payload per operation is:

| Case | First GEMM A / B bytes | Second GEMM A / B bytes | Copy calls, first / second | Explicit arena packing bytes |
| --- | ---: | ---: | ---: | ---: |
| Tiny F64 | 192 / 120 | 320 / 192 | 3 / 3 | 512 |
| Tiny complex | 384 / 240 | 640 / 384 | 3 / 3 | 1,024 |
| Small F64 | 4,760 / 1,496 | 3,080 / 520 | 4 / 3 | 7,840 |
| Small complex | 9,520 / 2,992 | 6,160 / 1,040 | 4 / 3 | 15,680 |
| Bulk F64 | 245,760 / 15,360 | 294,912 / 14,336 | 7 / 11 | 540,672 |
| Bulk complex | 491,520 / 30,720 | 589,824 / 28,672 | 10 / 15 | 1,081,344 |

Every actual copy invocation contributes its logical payload, including repeated
panels. Generated/C costs agree across lifecycle and caller-buffer reuse, batch
sizes 1/2/17 and all three Lean variants. All observed source routes here use the
packed path. Backend shortcut routes remain enabled; this record makes no claim
about their internal payload. Stock packing observations are null, not zero.
Explicit arena packing and backend copies are different operations; neither
channel measures physical memory traffic, cache effects or elapsed time.
The same-revision [Linux record](../2026-11-01-linux-packing/RESULTS.md) preserves
equal logical payloads for these cases but different packing call counts.

## Allocator and retained storage channels

The 936 observation processes retain **9,360 allocator snapshots**. All 312
`MI_STAT=2` processes have calibrated normal allocation deltas and agreeing empty
repeats. Their measured lifecycle run phases remain `3N+3` normal allocations /
`56N+64` binned bytes; prepared/reuse runs retain three fixed wrapper/control
objects / 64 bytes, not a per-call cost. The matched C run phases allocate zero
normal objects in the same Lean-hosted fixture. Checked failure includes the
actual two-object / 96-byte error payload. No further normal allocation is
unattributed within these measured diagnostic phases. Stock/rebuilt-zero normal
count summaries remain unavailable.

The 468 backend-diagnostic processes observe 6,768 pool borrows and matching
returns. Each process retains one 32 MiB mapping after cold work and releases it
at explicit shutdown. This is virtual backing capacity, not resident peak memory.
The calibrated named static pool declarations total **4,508 bytes**. The observers
are separate: source-call bridge 30,740 bytes, workspace observer 163,869 bytes,
packing observer 1,339,420 bytes, and allocator observer 43,732 bytes. Those sizes
exclude linker padding, code, strings, stack and reporting allocations.
Overlapping allocation channels must not be summed as independent costs.

## Verification and remaining gates

The full runner and independent directory/ZIP replay passed. All archived source
inputs match their Git blobs at `6abeee1`. The archive omits large source
executables and Lake caches but preserves their fingerprints; verification reads
evidence without executing archived code. Integrity and correspondence hashes
are not authenticity or native-refinement proofs.

All 64 tests passed with both `VASTITAS_SOURCE_ALLOCATOR_RECORD` and
`VASTITAS_SOURCE_PACKING_RECORD` selecting this archive:
`python3 -m unittest discover -s experiments/source_workspace -p 'test_*.py'`.
Mutations reject changed actual pointers, missing source footprints, relabeled
schemas, foreign runtimes and incomplete source/allocator coverage. Dependency
boundaries, whitespace and local Markdown targets also passed.
The subsequent 65-test publication suite passed with the Linux archive selected,
including independent replay of both retained schema-3 exports. This additional
publication regression does not change the measured source revision.

Operation clocks are disabled. This record does not measure initialization on
Lean's waiting startup thread, other allocators, all backend files, general heap
or meaningful whole-process/operation peaks. It does not transfer diagnostic
counts to a stock performance claim. Larger representative memory-bound workloads,
the predeclared tiny-call budget, unresolved slow paths and controlled Linux
measurements remain required by the [Stage 1 completion gate](../../../../docs/stage1-completion.md).
