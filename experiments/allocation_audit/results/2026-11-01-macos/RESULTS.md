# Generated resource allocation observations, macOS

**The bounded allocation audit passed. Performance and total-heap allocation were
not measured. Production runtime behavior is unchanged.** The private persistent
Unit-result experiment removes repeated FFI result allocations, but the emitted
`finally` then allocates a replacement result because the shared constructor is
not exclusive. That replacement and the retained singleton are counted below.

## Revision and retained records

Measured clean commit: `df16b7010cd4113bd3d832d5be68c32d6bd93c0b`.
Its production source includes diagonal metrics from main
`c394716a08f82b7f320c642fd14c5b55a6a3a8e9`; all changes in the measured feature
commit are confined to `experiments/allocation_audit`. Later evidence/report edits
are not assigned to the measured commit.

```sh
python3 experiments/allocation_audit/run.py \
  --prefix /private/tmp/vastitas-openblas-verified \
  --output /private/tmp/vastitas-allocation-final
```

The host was arm64 macOS, with Apple Clang 21.0.0 and Lean 4.35.0
(`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`). The static OpenBLAS 0.3.34 library was
LP64, sequential with locking and build-host CPU selection. Its exact binary hash,
frontend/kernel hashes, pinned Lean headers, build flags, and source hashes are
retained. No host timing comparison is made.

[evidence.zip](evidence.zip) contains **401 members, 690,485 bytes**, SHA-256
`740f6e6a142ae1bb67e5284892cd9daf45edf91126e127c5802ddfec711e2ae8`.
[manifest.json](manifest.json) records every member's size and hash. The archive
contains the exact emitted Lean and C, private instrumented sources, canonical
source/wire, failure wire and checked emit response, command logs, thread test,
source snapshots, and pinned headers. Compiler/native binaries are identified by
hash rather than embedded. Five byte-identical convenience copies are retained:

- [allocations.json](allocations.json)
- [cases.json](cases.json)
- [environment.json](environment.json)
- [status.json](status.json)
- [openblas-build.json](openblas-build.json)

The independent [verify.py](verify.py) imports no experiment code. It checks the
archive and plain copies, matches 35 source snapshots to the exact measured Git
commit, recomputes dimensional arena costs and object-count formulas, checks all
raw command outputs and pairs, and validates error/thread records. All 40 recorded
source/header/binary input hashes remained unchanged through the run.

```sh
python3 experiments/allocation_audit/results/2026-11-01-macos/verify.py
```

## Actual executions

Four fixtures cover real/complex × contiguous/padded storage, each with dimensions
`(i,k,j,a,b)=(2,3,4,5,6)`. Both private variants first pass canonical public
check/build/run and actual kernel emit. No independently fabricated source model
is used to justify acceptance.

- **96 allocation records / 48 generated–C output/cost pairs**: four cases,
  fresh/persistent variants, lifecycle/reuse, and 1/2/17 repetitions.
- **Eight checked-wire runtime failures**: one expected output bit is changed,
  accepted by the real checker/emitter, then rejected by native `expect`. The
  exact error survives; `finally` runs, all six arena allocations are freed,
  and the external finalizer runs once. No unexpected tracked object remains.
- **Four fresh-process concurrent tests**: eight distinct dedicated Lean task
  threads rendezvous before first use. Each process records exactly one
  singleton initialization and 8,001 uses, including a successful `finally`
  after a deliberately fresh error. The persistent payload remains Unit and
  nonexclusive.
- All canonical results are `0`; exhaustive coordinate/padding checks and
  generated/C hashes agree in the normal audit executions. Only the eight
  intentional frontend-capture commands reject; all actual builds/executions pass.
- Three experiment-transformation tests and eight existing tree-harness tests
  passed separately. The local kernel and frontend were built before integration.

These are not whole-process ASan/LSan results. The new audit's leak condition is
balanced final-reference releases for tracked objects plus actual zero live
arena data. Error payload internals, general runtime objects and backend pools
remain outside that condition.

## Observed object counts

The pinned API reports a successful one-field IO result as **16 object bytes**
and the arena external wrapper as **24 object bytes**. `lean_box(0)` itself is an
immediate scalar, not an allocation. Primitive integer/layout arguments use the
emitted unboxed ABI; no per-element Lean value is created by these operations.

The table covers the `run` phase with `N` repetitions. It includes per-batch
emitted loop constructors and the benchmark-begin result; it excludes the
separately recorded first-use/setup/cleanup phases.

| Generated path | FFI result objects | Arena external objects | Direct emitted-C constructors | Control results | Total observed object bytes |
| --- | ---: | ---: | ---: | ---: | ---: |
| Fresh lifecycle | `36N` | `N` | `2` | `1` | `600N + 64` |
| Persistent lifecycle | `N` | `N` | `N + 2` | `1` | `56N + 64` |
| Fresh reuse | `4N` | `0` | `2` | `1` | `64N + 64` |
| Persistent reuse | `0` | `0` | `2` | `1` | `64` |

The two ordinary batch constructors occupy 32 + 16 bytes. The extra persistent
lifecycle constructor occupies 16 bytes per iteration. Every nonpersistent
tracked object is balanced by a final-reference release at an instrumented
caller site. C's repeated native work has no tracked Lean allocation in `run`;
its surrounding harness and common generated first-use call are recorded outside
that phase.

The fresh lifecycle's 36 FFI results are new-arena, six allocate, nine fill, six
store, pack/GEMM/regroup/GEMM, three expect, six drop, and close. The new-arena IO
result always remains fresh because it carries an owned external object. Ordinary
successful operation results and close use Unit.

The first resource use records one external wrapper and 36 fresh results in the
baseline. In the experiment it records one fresh new-arena result, one external,
one emitted `finally` fallback, and the one-time **16-byte persistent singleton**.
That singleton remains intentionally live at the end. The observed peak is 72
bytes for fresh and 88 bytes for persistent; these are peaks of the bounded
tracked set, not total live Lean/process heap.

The persistent result cannot be reset in place. Retained `Emitted.c` shows the
`lean_is_exclusive` test and `lean_alloc_ctor` fallback after close. Consequently,
35 shared Unit returns per lifecycle eliminate 35 FFI allocations but introduce
one caller allocation. Reuse has four shared returns per iteration and no
per-iteration constructor fallback. This explains the object-count change, not
an elapsed-time change.

## Arena costs and exclusions

Both variants retain exactly six caller data allocations and two arena metadata
allocations per lifecycle, with 280 peak metadata bytes in this ABI. The reused
`run` phase allocates no arena data/metadata. Completed-cycle counters also retain
the common first-use lifecycle and the separate reused setup/cleanup cycle.
They are grouped by deletion phase, not by the instant each allocation occurred.

| Fixture | Peak arena data bytes | Lifecycle written bytes, one repetition | Copied bytes, one repetition |
| --- | ---: | ---: | ---: |
| real contiguous | 1,624 | 3,488 | 512 |
| real padded | 3,296 | 5,160 | 512 |
| complex contiguous | 3,248 | 6,976 | 1,024 |
| complex padded | 6,592 | 10,320 | 1,024 |

All 1/2/17-repetition costs match independent dimensional formulas. Padding,
packing bytes, written bytes, arithmetic order and source/output values are
unchanged by the private experiment. All arena data is freed.

The observer uses a fixed table and the pinned public object-size/exclusivity APIs.
It observes FFI wrappers and direct emitted-C constructors, with explicit control
classification; it does not intercept the allocator globally. Process argument
and module setup, recursive Lean-library allocations/frees, IO error strings,
external-class registration, mimalloc bookkeeping/backing pages, BLAS workspace
and packing, and OS mappings are excluded. `cold` means first resource use after
runtime/module initialization, not a proof of a cold backend or cold process.

No timing result from this instrumented executable is performance evidence. The
observer's table scans and added calls perturb execution, and no independent
uninstrumented timing run was performed here. This record supports a separately
reviewed production optimization investigation; it establishes neither zero
total allocation nor C parity, and does not pass the Fast like C gate.
