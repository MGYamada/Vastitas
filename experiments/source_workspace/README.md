# Checked source and backend workspace costs

This optional diagnostic connects the actual public two-edge contraction-tree
source to distinct observations in the same process: selected Lean
FFI/emitted-constructor objects, native arena data/metadata traffic, and the
pinned OpenBLAS `memory.c` pool/backing events around each actual CBLAS call.
Optional calibrated allocator, block lifetime and actual GEMM packing channels
are described below.
It does not change the compiler, public protocol, production runtime or numerical
backend. The older allocation schema-2 records remain separate and unchanged.

Retained full records at clean `605a5a7c82697bd53241983e8a42c03a68fd372a`:
[macOS](results/2026-11-01-macos/RESULTS.md) and
[Linux](results/2026-11-01-linux/RESULTS.md). Each has 312 observed executions and
24 canonical source executions. Later verifier regressions additionally reject
balanced churn in surrounding phases, mismatched generated/C backend costs,
changed stdin/backend bindings and unlisted archive files; the original measured
bytes/revision remain unchanged.

Build a stock/diagnostic pair with the [workspace calibration](../openblas_workspace/README.md)
from the **same observer sources** first. Its full verified record is required;
the exact archives, headers, observer inputs and unchanged calculation objects
are rechecked. The diagnostic prefix is linked only into private observed executables.
Every canonical public `check`, `build` and execution uses the stock prefix.

```sh
lake -d lean-kernel build
cargo build --locked
python3 experiments/openblas_workspace/run.py --out /tmp/workspace-record --build-dir /tmp/workspace-build --jobs 4
python3 experiments/source_workspace/run.py --prefix /tmp/workspace-build/stock --diagnostic-prefix /tmp/workspace-build/diagnostic --backend-record /tmp/workspace-record --output /tmp/source-workspace-record
python3 experiments/source_workspace/verify.py /tmp/source-workspace-record
python3 experiments/source_workspace/archive.py /tmp/source-workspace-record /tmp/source-workspace-compact/evidence.zip
python3 -m unittest discover -s experiments/source_workspace -p 'test_*.py'
```

On Linux add `--target HASWELL` to the backend calibration on a supported CPU.
Use new external scratch directories; records are never overwritten. Python
optimization (`-O`) is rejected because the inherited object checks use assertions.
The default full record has 12 tiny/small/bulk real/complex cases with/without
padding. `--smoke` selects four tiny cases and `--one-case` explicitly labels a
debug record; neither can masquerade as full coverage. The three fixed dimension
tuples are inherited from the existing tree experiment. Its largest fixture is
not evidence of a representative memory-bound performance workload.

`--streaming` selects a separate large-output profile using the same public tree
source, exact returned instructions, coordinate oracle and equivalent C work.
Its fixed `(i,k,j,a,b) = (512,2,2,64,512)` matrix covers real/complex and
padded/unpadded layouts. The result alone is 128 MiB / 256 MiB; total live arena
data is about 129 MiB / 258 MiB. Every result and padding cell is checked, with
explicit caller scratch, initialization, packing and complete lifecycle/reuse
costs. The small inner dimensions make this a candidate for memory-bandwidth
measurement, but capacity alone does not establish cache misses, DRAM traffic or
a bottleneck on a particular host. This diagnostic still has no operation clocks.

Streaming records use batches **1 and 2**, separately from the standard profile's
1/2/17, to stay within the calibrated packing observer's fixed capacity. Overflow
is fatal, never truncated or silently replaced by stock results. Full streaming
coverage with the allocator has 24 canonical executions, 192 normal observations
and 24 failure-cleanup processes. `--streaming --one-case` is explicitly labeled
`debug-streaming-one`; it cannot stand in for the complete four-case matrix.
`--smoke` and `--streaming` are mutually exclusive. Existing records and default
coverage remain unchanged. Use the same calibration command below with
`--streaming` and a new output directory; retain host/cache information separately
before drawing any memory-bound performance conclusion. No such acceptance is
implied by adding this profile.

The complete [macOS](results/2026-11-01-macos-streaming/RESULTS.md) and
[Linux](results/2026-11-01-linux-streaming/RESULTS.md) streaming records at clean
`ceff584` each retain all four cases, 24 canonical executions, 192 normal
observations and 24 failure cleanups. Their 20 / 24 observed source packing
contracts receive 80 / 96 separate plain/sanitized footprint executions. All 81
source snapshots match Git and each other. The 128/256 MiB outputs establish
large-output execution/cost coverage, with
operation timings and hardware traffic still unmeasured.

For every case and backend, the runner retains the manifest/source, original
protocol-8 wire, actual kernel response, exact returned Lean, observed wrapper,
emitted C and private native sources. A stdin digest binds each kernel invocation
to its actual wire; command context distinguishes same-argument invocations for
different cases. The unchanged public executable runs before observation. The
private wrapper uses the production once/persistent Unit helper and exact
returned instructions, with strict transformations inherited from the allocation
audit. A checked failure variant changes one expected bit, propagates the actual
native error, and verifies cleanup. These executions are empirical connections,
not a proof of wrapper/source or native refinement.

The standard full record contains 24 canonical public check/build/executions, 288 normal
observations and 24 failure-cleanup processes. Normal observations cover generated
and matched C operations, complete lifecycle and caller-buffer reuse, and batch
sizes 1, 2 and 17 on each backend. Each process first executes one cold generated
operation (two GEMMs), including the C comparison processes. The C path is the
existing competent contiguous-block-copy comparator in the Lean-hosted fixture;
it is not a standalone C startup/heap measurement. All numerical outputs, padding
and explicit arena costs must agree. Lean workers are disabled for executions;
builds use one worker because Lake requires its task manager. BLAS is sequential.

The bridge records real/complex kind, order, transforms, dimensions, leading
dimensions and exact alpha/beta bits at each actual CBLAS call. Diagnostic event
cursors bracket that call; replay checks complete, nonoverlapping attribution and
inside-call loan return. A pool return does not free its backing. Shutdown releases
retained mappings explicitly. The stock build has **null**, not zero, event
intervals. An observed empty interval means no events at these hooks; it does not
establish no internal packing, no other allocator use, or zero retained capacity.
The bounded bridge and backend buffers report their explicit static object sizes;
these exclude linker padding, stack, code, strings and report-time allocations.

Operation clocks are disabled. Inherited fields named `timed_*` denote the selected
run scope only; they carry no timing claim. `process_maxrss_kib` is retained as an
unisolated process diagnostic (including possible inherited high-water state),
excluded from cost equality and not used as meaningful per-operation peak memory.
In schema 1, general Lean heap/allocator traffic, backend static metadata and other
files, actual backend packing/copy bytes and residency remain unmeasured. These
records do not close total-cost, tiny-call budget or controlled-host acceptance
gates. Schemas 2 through 4 add the scoped channels described below.

The compact ZIP retains all source, command and raw observation evidence including
the nested backend calibration. Large Lean executables and Lake caches are omitted;
their exact executable hashes/sizes remain recorded. Verification reads archived
bytes without executing or extracting archived code. Hashes establish integrity
and correspondence, not authenticity or a proof about the native toolchain.

## Calibrated Lean allocator composition (schema 2)

The retained [macOS record](results/2026-11-01-macos-allocator/RESULTS.md) and
[Linux record](results/2026-11-01-linux-allocator/RESULTS.md) measure clean
`f0e0c55d79978d68021ba0ee0831916d1153606d`. Each contains 936 observed processes
and 72 canonical executions across all twelve cases and six configurations.
The diagnostic's normal allocations are explained by the selected sites plus
the actual error payloads within the observed phases; startup and general heap
coverage remain excluded. This is cost evidence, not timing acceptance.

The publication verifier additionally checks the actual linked support-library
paths against the calibration and replays both complete exports. Raw records
retain their measured revision; later verifier changes do not relabel it.

Supply a completed [Lean allocator calibration](../lean_allocation_diagnostic/README.md)
and its three actual runtime archives to observe calling-thread allocator phase
deltas alongside the existing channels:

```sh
python3 experiments/lean_allocation_diagnostic/run.py --out /tmp/lean-allocator-record
python3 experiments/source_workspace/run.py --prefix /tmp/workspace-build/stock --diagnostic-prefix /tmp/workspace-build/diagnostic --backend-record /tmp/workspace-record --lean-record /tmp/lean-allocator-record --lean-runtime-dir /tmp/lean-allocator-record/build --output /tmp/source-allocator-record
python3 experiments/source_workspace/archive.py /tmp/source-allocator-record /tmp/source-allocator-compact/evidence.zip
VASTITAS_SOURCE_ALLOCATOR_RECORD=/tmp/source-allocator-compact/evidence.zip python3 -m unittest discover -s experiments/source_workspace -p 'test_*.py'
```

Linux requires Clang and the libc++/libc++abi development packages used by the
calibration. The optional arguments must be supplied together. Omitting them
retains schema 1 and its original two-backend coverage; existing records keep
their measured bytes, revisions and claims.

Schema 2 crosses both backends with stock, rebuilt `MI_STAT=0`, and diagnostic
`MI_STAT=2` Lean runtimes. The full twelve-case matrix has 72 canonical public
check/build/executions, 864 normal observations and 72 failure-cleanup processes.
All canonical executables use the installed stock Lean runtime and stock backend.
Only private observation executables select a calibrated runtime. Each linker map
must name that exact archive; the nested calibration audits its single changed
object, all unchanged members, build flags, toolchain/header fingerprints and
known-allocation experiments. Rebuilt zero is a control, not a claim of byte
identity with the installed object. Private variants must preserve outputs, arena
costs, selected objects and actual CBLAS calls. Diagnostic backend replay must
agree across Lean variants, and allocator deltas must agree across backends.

The additional static observer takes two immediate snapshots at five boundaries:
before cold execution, after cold, after setup, after the run, and after cleanup.
The pair must have identical counter values. No counter reset, forced collection,
printing or dynamic observer allocation occurs inside these phases. The final
snapshot precedes all reporting. `LEAN_NUM_THREADS=0` and `LEAN_MAIN_USE_THREAD=1`
pin the observed execution profile. The fixed observer objects occupy 43,732 bytes;
this excludes alignment, code, strings, stack and reporting costs.

The diagnostic compares normal allocation counts/binned bytes with the existing
selected sites. The actual error payload is inspected before construction of the
already-tracked error result: one 16-byte `IO.Error` constructor and a string with
76 requested / 80 usable bytes (44 UTF-8 bytes including its terminator). Their
two allocations / 96 binned bytes are separate from the selected error-result
object and explain the additional channel in the retained checked failure runs.
The verifier retains any further unattributed allocation explicitly. Counts and
bytes from overlapping channels must never be added together as separate costs.

Only the diagnostic has calibrated transient normal counts. Stock/rebuilt-zero
summaries use **null**, while retaining their raw values; zero raw counters do not
mean zero allocation. Requested-byte counters remain incomplete and cumulative,
and raw peaks are not interpreted as per-operation or whole-process peaks.
Current-byte **changes** may include release of command arguments that were live
before the baseline. A negative change is not a negative allocation or a leak.
Lean's waiting initialization thread has unmerged startup statistics, so its
allocations are outside this channel. In schema 2, other allocators, backend
packing and static metadata, residency, general peaks, other source profiles and
controlled-host timing remain separate gates. This experiment establishes no
native refinement or transfer of diagnostic counts to a stock runtime performance
claim.

## Actual source GEMM packing composition (schema 3)

The retained [macOS](results/2026-11-01-macos-packing/RESULTS.md) and
[Linux](results/2026-11-01-linux-packing/RESULTS.md) records both measure clean
`6abeee14b708e9bc1752c420949043971dc48a28`: each has 72 canonical executions,
936 observation processes and 13,536 actual CBLAS calls. All 70 / 66 source-observed
packing contracts receive separate plain/sanitized stock/diagnostic footprint
checks. Logical payload agrees for the retained cases while actual copy-call
counts differ. Both preserve the allocator channel and add no operation timing
or completion claim.

After Unit-only cleanup, the complete
[macOS](results/2026-11-01-macos-unit-cleanup/RESULTS.md) and
[Linux](results/2026-11-01-linux-unit-cleanup/RESULTS.md) records measure clean
`84b0c115f1a003edf52d4634c9dbebbbf6531b18`. Each preserves the standard twelve-case,
six-configuration coverage and 9,360 allocator snapshots. Lifecycle batches
1/2/17 observe 5/7/37 normal allocations and 104/144/744 binned bytes; reuse
remains three / 64 per batch. All 81 source snapshots match Git and each other.
Actual source packing uses 72 / 66 contracts, checked by 288 / 264 additional
plain/sanitized footprint executions. The older records above keep their charged
`finally` fallback; the new diagnostic counts are not stock total-heap or timing
claims.

A completed schema-2 [packing calibration](../openblas_packing/README.md) can now
replace the workspace-only backend calibration. The runner detects its record
kind and emits source schema 3. It preserves schemas 1 and 2 and their archived
measurements. This private diagnostic schema does not change a public wire version.

```sh
python3 experiments/openblas_packing/run.py --out /tmp/packing-record --build-dir /tmp/packing-build --jobs 4
python3 experiments/source_workspace/run.py --prefix /tmp/packing-build/stock --diagnostic-prefix /tmp/packing-build/diagnostic --backend-record /tmp/packing-record --lean-record /tmp/lean-allocator-record --lean-runtime-dir /tmp/lean-allocator-record/build --output /tmp/source-packing-record
python3 experiments/source_workspace/archive.py /tmp/source-packing-record /tmp/source-packing-compact/evidence.zip
VASTITAS_SOURCE_ALLOCATOR_RECORD=/tmp/source-packing-compact/evidence.zip VASTITAS_SOURCE_PACKING_RECORD=/tmp/source-packing-compact/evidence.zip python3 -m unittest discover -s experiments/source_workspace -p 'test_*.py'
```

The two Lean-calibration arguments remain optional. With them, the same twelve
cases and six backend/runtime configurations include the calibrated allocator
channel. Without them, schema 3 observes the two backend configurations. Every
canonical public executable continues to use the stock backend and installed
Lean runtime. Linux requires the explicit supported HASWELL backend target.

Each actual CBLAS wrapper captures its three matrix addresses as well as its
existing shape, stride, transform, coefficient and event interval. Replay requires
one corresponding backend route with those exact addresses and arguments. It
checks every actual copy's source rectangle, live destination pool loan and
complete input coverage, charging repeated packing again. Addresses are compared
inside the same execution; generated/C and runtime-variant comparisons use
logical cost and route records, not process addresses.

The source can exercise shapes or leading dimensions absent from the backend's
calibration fixtures. The runner therefore reconstructs every distinct observed
`(kernel, m, n, lda)` contract and checks it separately against both calibrated
archives, using plain and ASan/UBSan harnesses. It compiles the current trusted,
fingerprinted calibrator, never archived binaries. Exact source, compile/link,
execution and output-footprint receipts remain in the record; the four executable
hashes/sizes remain under `packing.binaries`, while their files are omitted from
compact exports. Upstream kernel objects themselves are not sanitizer-instrumented.

The bridge and packing observers use fixed storage and report after the allocator's
final snapshot. Stock packing observations are null. GEMV/small shortcuts retain
unavailable payload measurements; no shortcut is disabled. The reported logical
packing payload, named backend static pool metadata, and each observer's own bytes
remain separate from arena traffic, Lean allocation and workspace capacities.
The original broad `backend_packing_bytes` claim remains false: the additional
`packing.claims.logical_packing_payload` identifies only the observed D/Z copy
calls, not shortcut internals or all backend traffic. There are no operation
timings, hardware-traffic measurements, whole-process peaks or controlled-host
acceptance claims.

The source-cost CI uses the schema-4 extension below on macOS and Linux for both push
and pull_request. Superseded runs are cancelled within each event/branch; the
two current event runs remain independent. Retained schema-1/2 replay and mutation
tests continue to run alongside the new address/route/footprint regressions.

## Source block lifetimes and transient peaks (schema 4)

The retained macOS [standard](results/2026-11-02-macos-lifetimes/RESULTS.md) and
[large-output](results/2026-11-02-macos-lifetimes-streaming/RESULTS.md) records
measure clean `8212d7d0a6720e37913b6d44d5932e8ff263ead8`. Their 86 source inputs
are identical and match Git. They retain 96 / 32 canonical executions,
1,248 / 288 observation processes and 1,560 / 360 lifetime boundary pairs.
Generated lifecycle interval peaks are 72 usable bytes above entry, reuse is
48 and checked failure is 136 in these private runtime records. These are
logical-block costs, separately from native arenas, backend backing and observer
storage. Linux confirmation is pending; no timing acceptance is inferred.

Supply the separate [block lifetime calibration](../lean_allocation_lifetimes/README.md)
and its exact runtime archive and observer object to add the private `lifetimes`
variant. This requires the three existing Lean controls and actual packing
calibration. It extends the private source-cost record, not public protocol 8.

```sh
python3 experiments/lean_allocation_lifetimes/run.py --out /tmp/lean-heap-record --mimalloc-archive /tmp/lean-allocator-record/inputs/mimalloc-v3.4.5.tar.gz
python3 experiments/source_workspace/run.py --prefix /tmp/packing-build/stock --diagnostic-prefix /tmp/packing-build/diagnostic --backend-record /tmp/packing-record --lean-record /tmp/lean-allocator-record --lean-runtime-dir /tmp/lean-allocator-record/build --heap-record /tmp/lean-heap-record --heap-build-dir /tmp/lean-heap-record/build --output /tmp/source-heap-record
python3 experiments/source_workspace/archive.py /tmp/source-heap-record /tmp/source-heap-compact/evidence.zip
VASTITAS_SOURCE_ALLOCATOR_RECORD=/tmp/source-heap-compact/evidence.zip VASTITAS_SOURCE_PACKING_RECORD=/tmp/source-heap-compact/evidence.zip VASTITAS_SOURCE_HEAP_RECORD=/tmp/source-heap-compact/evidence.zip python3 -m unittest discover -s experiments/source_workspace -p 'test_*.py'
```

Both backends now cross four runtime variants: stock, rebuilt zero-statistic,
diagnostic statistics, and calibrated lifetimes. A full standard record requires
96 canonical public executions, 1,152 normal observations and 96 failure cleanups.
The separate streaming profile requires 32 / 256 / 32 respectively. Canonical
executables still use the unchanged stock backend and installed Lean runtime.
Schemas 1 through 3 and their retained records keep their original coverage.

Only the fourth variant exposes process-global logical mimalloc block traffic,
live usable bytes and simultaneous usable-byte peaks. Five before/after pairs
bracket the existing statistics observer and an independent main-heap walk.
The pair must match exactly; live block counts and usable bytes must equal the
walk. Each checkpoint closes one interval and resets only its peak to current
live bytes under the same observer lock. Allocations, frees, live state and the
global peak are never reset. Cold/setup/run/cleanup traffic must agree with the
independent calling-thread `MI_STAT=2` channel. Repeated backend runs compare
traffic and peaks above the interval's entry live set, preserving each process's
distinct startup state.

The first snapshot includes module initialization and argument parsing before
cold execution. It is retained as an absolute state, not subtracted away and
called zero allocation. Phase entry and exit live bytes, acquired/released usable
bytes, low-level allocation request bytes and the interval peak remain distinct.
For example, releasing preexisting command arguments can decrease live bytes
while the phase still allocates. Selected objects and actual error payloads are
contained in the global channel; any remaining allocations or releases are
explicit. Overlapping allocation channels must not be added together, nor may
independent subsystem peaks be summed as a simultaneous whole-process peak.

The complete nested calibration binds both the rebuilt `libleanrt.a` and the
separate `lifetime.o` through exact hashes, toolchain inputs, linker maps and
source/header receipts. Only that variant builds the phase hooks. Its observer
adds 4,194,417 bytes of static calibration storage and 1,208 bytes of phase
snapshots/guards, in addition to the existing 43,732-byte statistics observer.
These are declared object sizes, excluding padding, stack, code and report costs.
All reporting follows the final snapshot; there is no forced collection or
observer allocation within a measured interval. Capacity exhaustion is fatal.

These are private allocator observations, not stock-runtime counts or timings.
They cover logical blocks, not physical allocator backing, libc/GMP or all
process allocations. Report generation and process teardown are outside the
final boundary. The C comparator is still Lean-hosted, not a standalone C
startup comparison. Full cost attribution, controlled-host bulk measurements,
the predeclared tiny-call budget and native refinement remain separate gates.

Cleanup cost expectations follow each actual returned source. Replay rebuilds
the complete allocation wrapper with trusted code, preserving either the older
`finally` envelope or current Unit-only close/rethrow cleanup. It checks both
normal and failure bodies and requires the common cleanup helper among the new
record's fingerprinted inputs. The retained schema-1/2/3 records keep their
measured code and counts; support for a new envelope is not new measurement or
performance evidence.
