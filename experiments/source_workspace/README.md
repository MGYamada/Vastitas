# Checked source and backend workspace costs

This optional diagnostic connects the actual public two-edge contraction-tree
source to three distinct observations in the same process: selected Lean
FFI/emitted-constructor objects, native arena data/metadata traffic, and the
pinned OpenBLAS `memory.c` pool/backing events around each actual CBLAS call.
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

The full record contains 24 canonical public check/build/executions, 288 normal
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
General Lean heap/allocator traffic, backend static metadata and other files,
actual backend packing/copy bytes and residency remain unmeasured. These records
do not close total-cost, tiny-call budget or controlled-host acceptance gates.

The compact ZIP retains all source, command and raw observation evidence including
the nested backend calibration. Large Lean executables and Lake caches are omitted;
their exact executable hashes/sizes remain recorded. Verification reads archived
bytes without executing or extracting archived code. Hashes establish integrity
and correspondence, not authenticity or a proof about the native toolchain.
