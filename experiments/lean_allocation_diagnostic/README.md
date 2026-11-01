# Diagnostic Lean allocator calibration

This optional experiment compares the installed Lean 4.35.0 runtime with two
private copies of its runtime archive. In each copy, only `mimalloc.cpp.o` is
rebuilt from pinned upstream sources: one with `MI_STAT=0`, the other with
`MI_STAT=2`. Every other runtime object must remain byte-identical and in the
same archive order. The installed toolchain is never changed. The locally rebuilt
zero-statistics object is **not** claimed byte-identical to the installed object;
its compiler, flags, SDK and standard-library inputs may differ.

The five calibrated workloads are constructors, medium and huge ByteArrays,
closures with an immediate captured value, and arrays of immediate values.
They use actual public Lean allocation and reference-counted release APIs.
Each workload has held, released and transient phases. Three fresh processes per
runtime variant retain 162 snapshots, including repeated empty observations and
an explicitly separate forced collection. Known retained addresses, block counts,
`mi_usable_size`, checksums and independent counter arithmetic must agree.

The [retained macOS record](results/2026-11-01-macos/RESULTS.md) measures clean
`54531c11b2843a0d3d7565b71e7463e4387b8c03`: all five diagnostic transient counts
and known releases agree, with 34 unchanged runtime objects. Stock/rebuilt-zero
normal counters have no signal. These are calibration results, not total heap or
stock-production allocation evidence.
The separately [retained Linux record](results/2026-11-01-linux/RESULTS.md) measures
the corresponding clean CI test merge `5425c1a`, independently matched to the same
source tree. Both records pass the 15 focused verifier/provenance tests.

```sh
python3 experiments/lean_allocation_diagnostic/run.py \
  --out /tmp/vastitas-lean-diagnostic-new --cc cc --cxx clang++
python3 experiments/lean_allocation_diagnostic/verify.py \
  /tmp/vastitas-lean-diagnostic-new
VASTITAS_LEAN_DIAGNOSTIC_RECORD=/tmp/vastitas-lean-diagnostic-new \
  python3 -m unittest discover -s experiments/lean_allocation_diagnostic -p 'test_*.py'
```

The output directory must be new and outside the checkout. A cached download can
be supplied with `--mimalloc-archive`; its SHA-256 is checked before extraction.
The builder needs a host C++20 compiler. Linux uses Clang with libc++ headers
(`libc++-dev` and `libc++abi-dev` on the CI image), matching Lean's C++ library
family. macOS uses the installed Apple toolchain. The bundled `leanc` C compiler
alone does not supply C++ headers. No mathlib, OpenBLAS or runtime installation
modification is required. `LEAN_NUM_THREADS=0` prevents creation of Lean task
workers. `LEAN_MAIN_USE_THREAD=1` explicitly retains the pinned runtime's ordinary
[entry thread](https://github.com/leanprover/lean4/blob/v4.35.0/src/runtime/thread.cpp#L186-L202):
the initialization thread waits in `join` while the single probe mutator runs.
The probe creates no additional threads. Child processes clear `MIMALLOC_*` overrides
and reject preload interposition, while other ordinary host environment and SDK
dependencies remain external.

## What is and is not measured

`MI_STAT=2` instruments the same translation unit that includes the allocator's
inlined small-object path. This is a diagnostic build, not a stock-production
allocation or timing measurement. The stock variant reports the actual available
signals without assuming its compile-time flags.

| Channel | Calibration contract | Limit |
| --- | --- | --- |
| Main-heap block visitor | Each known held address appears once; counts and usable bytes return to baseline after release | Only sampled main-heap objects; no universal churn or peak claim |
| Diagnostic normal/huge allocation counts and binned bytes | Known allocation totals and releases agree for all five workloads | Does not cover system malloc, GMP payloads, other allocators, arbitrary object types or concurrent heaps |
| `malloc_requested` | Normal requests accumulate; huge requests are absent and free does not decrement it | Neither complete requested bytes nor live bytes, even in the diagnostic build |
| Allocator peak/backing fields | Preserved raw as separate diagnostics | No general peak, RSS, residency or additivity claim |

The observer uses fixed static storage, warmed before the baseline, prints only
after all measured phases, and creates its returned IO result afterward. It does
not reset statistics. Repeated observations must add no allocation signal.
Observer buffers/tables are reported separately; their bytes exclude code,
alignment, strings, stack and reporting. No operation clocks are sampled.

The calibration concerns **changes after the baseline**. Startup counts and the
baseline visitor's total need not coincide: `mi_stats_get` merges the calling
thread's current heap statistics and already merged statistics, not the still-live
initialization thread's unmerged counters. The heap visitor can see its retained
objects. This difference is not promoted to a startup coverage claim. Likewise,
requested `current` staying high after release is not
evidence of retained objects. Normal and huge peak fields cannot simply be added
to get a simultaneous live peak; cross-thread aggregation introduces further
limits. This experiment does not close the whole-program cost gate.

## Provenance and review

[upstream-sources.json](upstream-sources.json) records Lean and mimalloc pins.
The five vendored Lean files are unmodified upstream blobs with their Apache 2.0
license. The complete mimalloc release archive includes its MIT license. The
statistics header and strict JSON helpers are shared with the unchanged
[stock calibration](../stock_allocation_capabilities/README.md).

The record retains sources, installed headers, stock and replacement runtime
archives, emitted C, object files, binaries, linker maps, commands, raw streams
and parsed observations. The verifier reads BSD/GNU archive bytes independently,
requires exactly one changed member, checks selected archive paths in the linker
maps, pairs the two rebuild commands, and rejects missing phases or unsupported
claims. Toolchain libraries are fingerprinted before/after; system C++ headers,
SDKs and libc are external toolchain dependencies. Hash inventories detect
corruption, not forged measurement evidence or native correctness. Retained ZIPs
can be checked without extraction or executing their contents.

The [source/backend composition](../source_workspace/README.md) now binds these
archives to actual generated source/FFI phases. The separate
[block lifetime calibration](../lean_allocation_lifetimes/README.md) addresses the
startup/live-peak blind spots with a private global observer; it does not change
the meaning of these older records. Full allocation/peak attribution and
controlled-host performance remain open in
[the completion gate](../../docs/stage1-completion.md).
