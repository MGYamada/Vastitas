# Actual production shared-Unit allocation audit, macOS

The schema-v2 four-case audit passed on 2026-11-01. It observes the actual
`vastitas_io_unit_success` implementation using supported pinned Lean
`lean_obj_once` and explicit `lean_mark_persistent`. It does **not** substitute
the earlier pthread prototype. No timing, total-heap, speedup or Fast like C
acceptance claim is made.

The measured base was `24b5f3166c020a38d941e6140338a6ec08e1f3a8`, with uncommitted
production shared-result and audit changes. The exact dirty-path listing is in
[environment.json](environment.json). This record belongs to those retained
inputs, not a later commit or main integration. Forty selected source/input
snapshots, the pinned Lean headers, actual frontend/kernel binaries and OpenBLAS
archive were hashed: all 45 hashes remained unchanged through the run. Public
and private emitted Lean/C plus the exact instrumented native inputs are retained.

The [original record](../2026-11-01-macos/RESULTS.md), its archive and its verifier
are byte-for-byte unchanged. They still describe the earlier pthread experiment.

```sh
python3 experiments/allocation_audit/run.py \
  --prefix /tmp/vastitas-openblas-verified \
  --output /private/tmp/vastitas-production-unit-final
python3 experiments/allocation_audit/verify.py \
  experiments/allocation_audit/results/2026-11-01-macos-production/evidence.zip
python3 -m unittest discover -s experiments/allocation_audit -p 'test_*.py' -v
python3 experiments/allocation_audit/results/2026-11-01-macos/verify.py
```

## What was executed

The four actual two-edge contraction-tree fixtures cover real/complex and
contiguous/padded layouts. Each executes explicit pack, GEMM, regroup and GEMM
with six caller-owned allocations. Both variants first perform unmodified public
check/build/run and actual kernel emission. There are eight such public builds,
eight private wrapper builds, 96 allocation records and 48 generated–C
output/cost pairs across lifecycle/reuse scopes and 1, 2 and 17 repetitions.
Every independent dimensional arena-cost recomputation and output/cost comparison
passed. All six buffers are freed at each completed lifecycle.

- `production_shared` observes allocation **inside the actual initializer** and
  each actual return after `lean_inc`. The original `lean_obj_once` publication
  and `lean_mark_persistent` remain intact. The transform requires an exact full
  helper/initializer envelope and fails on unfamiliar or duplicated input.
- `private_fresh` is an explicitly experimental comparator: only its copied
  helper envelope returns a new Unit-success object each time. Callers and
  status/error checks remain unchanged. It is neither a production build nor a
  reinterpretation of the older measured compiler.
- The old `persistent.c` is not compiled by the schema-v2 run. It is retained as
  historical source; none of its pthread counts are used as production evidence.

Eight failure executions mutate one expected output bit, pass the modified wire
through the actual checker/emitter, and execute it. Each propagates the exact
`E_NATIVE_EXPECT` error, completes `finally`, finalizes its arena, frees all six
buffers and leaves no unexpected tracked object. The shared variant retains
only its intended Unit singleton. Errors remain fresh.

Four additional fresh processes compile the actual production native FFI with
one atomic initializer observation. Eight dedicated Lean task threads rendezvous
before first use; distinct TLS identities establish distinct live workers. Each
process checks exactly one actual initializer and 8,001 helper uses: 8,000 worker
calls plus a `finally` call after a real `E_NATIVE_HANDLE` error. The original
error is preserved. Two actual new-arena IO results, two stats IO results and
two native error results are separately checked to be distinct, exclusive and
nonpersistent; successful Unit payloads remain unchanged and nonexclusive.

At measurement, seven transformation/domain/retention regression tests passed. The standalone
v2 verifier checks exact cases, variants, scopes and repetitions, all returned
uses and balances, native costs, actual command outputs, source hashes, full
archive member hashes and the five plain copies. The old record's independent
verifier also still passes.

After measurement, independent review found that the verifier accepted an extra
fully released error-result object in the run phase: balance alone did not check
the reported total allocation cost. The current verifier now checks total run
object counts/bytes, absent error/persistent allocations, implementation-specific
peaks and nonnegative exact-integer counter domains. Eleven tests pass, including
mutations of those fields with matching command stdout. The archive and raw
measurements are unchanged; its earlier verifier/test snapshots remain the
measurement provenance, rather than the later validation code.

## Actual scoped counts

The first resource lifecycle after Lean/module initialization constructs one
16-byte persistent Unit result and returns that same object 35 times. Its other
tracked cold allocations are a 16-byte newArena IO result, a 24-byte external
arena wrapper, a 16-byte emitted `finally` fallback and a 16-byte marker result.
The singleton remains intentionally live for process lifetime and retains no
arena/error payload. This is resource-call first touch, not all process startup.

For N later repetitions, the observed `run` phase contains:

| Tracked fresh allocation | Production shared | Private fresh comparator |
| --- | --- | --- |
| Lifecycle FFI IO results | N × 16 bytes, carrying each new arena | 36N × 16 bytes |
| Lifecycle arena external objects | N × 24 bytes | N × 24 bytes |
| Lifecycle emitted `finally` fallback | N × 16 bytes | 0 |
| Lifecycle loop/batch constructors and control result | 64 bytes per batch | 64 bytes per batch |
| Lifecycle total tracked fresh bytes | **56N + 64** | **600N + 64** |
| Reuse FFI Unit results | 0 fresh objects; 4N shared returns | 4N × 16 bytes |
| Reuse loop/batch constructors and control result | 64 bytes per batch | 64 bytes per batch |
| Reuse total tracked fresh bytes | **64** | **64N + 64** |

The production lifecycle also returns the shared object 35N times. Counts include
the caller effect of nonexclusivity: generated `finally` cannot reset the shared
close result and allocates its ordinary fallback. That allocation is retained in
the table and actual emitted C. It is not subtracted as incidental overhead.

Reuse explicitly hoists setup and cleanup. Its 64-byte run-phase result does
not mean the entire process, setup or cleanup allocates nothing. The complete
phase ledger remains in [allocations.json](allocations.json). Completed-arena
totals are charged to the phase where deletion occurs, not retroactively to each
allocation's phase.

Tracked live bytes finish at 16 for production and zero for the private fresh
comparator. Maximum simultaneously tracked object bytes are bounded at 88 and
72 respectively across all cases and repetition counts. The persistent object
therefore slightly increases this scoped peak despite reducing repeated result
allocation. Arena data, packing/copy/write costs, six data allocation/free events
per lifecycle, and two metadata allocation events (280 peak metadata bytes on
this host) remain identical between generated and matched C work.

## Coverage and limits

These are actual observed Lean object sizes from `lean_object_byte_size` and
final-reference release sites in instrumented FFI/emitted C, plus separate arena
counters. They are **not total Lean heap or malloc bytes**. The observer excludes
process/argument/module startup, recursive allocation inside Lean libraries
(including once machinery), error-payload strings, external-class registration,
allocator backing/metadata, BLAS private workspace/packing and OS mappings.
Its pointer table performs no dynamic allocation but deliberately adds expensive
observation work. Elapsed fields inherited from the tree harness are invalid
for performance comparisons.

The record is macOS arm64 using the repository-pinned Lean 4.35.0 APIs and
sequential LP64 OpenBLAS 0.3.34. It is not Linux evidence. This allocation audit
does not run ASan/LSan and does not replace the separate native cleanup/sanitizer
suite. Final-reference accounting covers the stated tracked objects, not every
possible leak or client. API/publication checks and these executions are not a
proof of full source/native refinement or all platforms.

## Retained artifact

[evidence.zip](evidence.zip): 429 members, 736,611 bytes; SHA-256
`2f4768649e99dae68f878a17f5d2bdf06837410ac9ddfb4a2c07e72cafe502b7`.
[manifest.json](manifest.json) lists all member sizes/hashes and five plain JSON
copies. The archive retains actual source/wire/emission, instrumented C inputs,
emitted caller C, production-thread sources, pinned headers, command logs and
all records. Executables/object/static-library files are omitted; the measured
frontend/kernel/backend archive identities are in the environment.

The current [standalone verifier](../../verify.py) passes both the original run
directory and this archive: schema 2, 96 records, 48 pairs, 40 source snapshots,
8 failure cleanups and 4 production-thread processes. No preliminary one-case
run is used in place of this final four-case record.
