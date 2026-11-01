# Short regroup blocks: local native adapter comparison

The final change coalesces a common contiguous axis only when its byte width
is 16–64 and its extent is greater than one. Fixed-width byte copies allow the
compiler to inline the short transfers. Larger widths and incompatible physical
strides retain the original cell loop. All preflight, padding, alias, payload
and byte-accounting contracts remain.

This record compares two versions of the **native regroup adapter**, not
Vastitas against equivalent C and not the full generated operation. It supports
a bounded implementation choice. It does not close the Fast like C gate.

## Source, host and scope

The old source is `618508530cdd191ebe9a18d5ce6a9d03dc96c9a7`.
The final source is clean integrated commit
`2a59bdbd5262de386a018e5ad0befae6a762cac3`, after feature commit `7ca2767` and
merged measurement PR #356. The clean check before/after and source/header
stability are retained. The three preliminary runs explicitly retain modified
source snapshots and diffs against `6185085`; they are not clean-commit runs.

Host: Apple M4, macOS 27.2 arm64, Apple clang 21.0.0; CPU identification was
queried after the preliminary runs and immediately before the clean run.
The exact OS/compiler strings remain in each `record.json`. This is an
uncontrolled local host, with no CPU isolation or frequency guarantee.
Both objects use `-std=c11 -O3 -fno-lto -Wall -Wextra -Werror`. All old public
symbols are renamed in its private translation unit, so both implementations
run in the same process with separate identically prepared arenas. The ABI
header is byte-identical at both revisions. No Lean, FFI or BLAS runtime is
linked into this probe.

The fixed regroup is `[0,1 | 2]` to `[0,2 | 1]`. Extents are tiny `(2,4,5)`,
small `(7,5,11)` and bulk `(24,32,48)`, crossed with F64/complex and two
padding profiles. Each sample times repeated adapter calls, including native
preflight and return-status checks. Allocation, initialization, output checks
and cleanup are outside the timer. Each implementation's arena is reused.
Compiler latency, RSS and total allocator costs are not measured by this probe.
Counter deltas check exact copied/written volume and unchanged allocation/live
bytes; endpoint payload assertions prevent an unused-output benchmark.
The probe's constant input and endpoint checks are **not** the full coordinate
oracle. That separate regression is described below.

Both sides use the same repetitions and alternate order. Calibration doubles
repetitions until both sides reach 8 ms, then retains eleven measurement pairs
per case. Calibration also warms the path; there is no separate warmup phase.
The very shortest calibration batches can read zero at clock resolution; they
are retained and doubled, never used in a measured ratio. The clean run has
54 such calibration rows. No measurement batch in any retained run is below
8 ms, and no measured row was removed. Pair ranges below are observations,
not host-level confidence bounds.

## All completed runs remain retained

| Record | Source | Raw rows / measurement pairs | Observation |
| --- | --- | --- | --- |
| `variable_copy` | Modified `6185085` | 658 / 132 | Variable-length memcpy for every contiguous axis made tiny 2.1806–2.6419× slower than its paired old implementation. This was rejected. |
| `unbounded_fixed` | Modified `6185085` | 664 / 132 | Fixed short copies helped tiny/small, but larger complex blocks retained 1.0161–1.0344× overhead. This was not the final implementation. |
| `short_dirty` | Modified `6185085` | 660 / 132 | Coalescing restricted to short widths; tiny 0.7101–0.8200×, small F64 0.5285–0.5367×, bulk 0.9949–1.0014×. |
| `short_clean` | Clean `2a59bdb` | 660 / 132 | Final source, exact table below. This later run does not replace the earlier samples or their provenance. |

[evidence.zip](evidence.zip) preserves all four original data directories,
compiled C snapshots, header, objects/executables, compiler/execution commands,
raw pairs, summaries and metadata, plus the final launcher. It contains
**45 members / 197,024 bytes**, SHA-256
`860ced38fb5b758a6089b4b35f8f7b6a37945ef4ca04bc0a9507bd5c4c23578c`.
[artifact-manifest.json](artifact-manifest.json) hashes every member. The two
plain final [raw](raw.csv) and [summary](summary.json) files match the archive.
Retained executables are host-specific evidence, not portable tools. Rebuild
from each subtree's recorded compiler commands to repeat that snapshot; replace
the final absolute executable path with the rebuilt local `./probe` path.

## Final paired observations

A ratio below one means this adapter version was faster than the old adapter
in that pair. Deltas are new minus old. They exclude source/FFI and full-lifecycle
costs and cannot be subtracted from a separate tree benchmark.

| Size / scalar / padding | Paired new/old median | Observed pair range | Median delta, ns |
| --- | ---: | --- | ---: |
| tiny / F64 / 0 | 0.7149 | 0.7041–0.7453 | -8.2 |
| tiny / F64 / 1 | 0.7039 | 0.6881–0.7296 | -8.6 |
| tiny / complex / 0 | 0.8129 | 0.7926–0.8274 | -5.3 |
| tiny / complex / 1 | 0.8190 | 0.8026–0.8498 | -4.9 |
| small / F64 / 0 | 0.5045 | 0.4392–0.5382 | -54.0 |
| small / F64 / 1 | 0.5165 | 0.4767–0.5231 | -50.7 |
| small / complex / 0 | 0.9980 | 0.9737–1.0219 | -0.3 |
| small / complex / 1 | 1.0009 | 0.9842–1.0288 | +0.1 |
| bulk / F64 / 0 | 1.0011 | 0.9920–1.0047 | +8.3 |
| bulk / F64 / 1 | 0.9910 | 0.9579–1.0293 | -65.4 |
| bulk / complex / 0 | 1.0024 | 0.9879–1.0111 | +27.3 |
| bulk / complex / 1 | 1.0067 | 0.9925–1.0444 | +77.1 |

The short cases improve within this local comparison. Small complex and bulk
use the preserved cell loop; their small positive/negative differences do not
establish parity, a universal speedup or controlled-host stability. The final
bulk complex padded median is still +77.1 ns and an observed pair reaches
1.0444×. The source width cutoff is an implementation choice informed by these
native experiments, not a widened performance acceptance budget.

## Independent verification and safety coverage

Run the standard-library consistency audit, with both measured Git commits
available locally:

```sh
python3 experiments/contraction_trees/results/2026-11-01-macos-regroup-blocks/verify.py
```

It rebuilds/runs nothing. It checks the complete ZIP/inventory, exact old/header
and final C snapshots against Git, all four command recipes and raw stdout,
1,321 alternating pairs, twelve subjects per run, adaptive repetition counts,
all 528 measurement pairs and the recomputed per-pair ratios/deltas/medians.
The original launcher is archived as evidence; this verifier is independently
written and does not import its calculations.

Separate final-source validation passed `lake -d lean-kernel build`,
`bash scripts/check_storage_native.sh`, and
`VASTITAS_TEST_OPENBLAS_PREFIX=<pinned-prefix> cargo test --locked --test tree_source -- --include-ignored`.
The latter passes all nine tests, including 25 real-source check/build/executions
containing real and complex trees, all selected contraction orientations, empty
axes, branch arms and cached producers. The native ASan/UBSan matrix covers
144 regroup pairs × twelve shapes × two padding profiles × two scalars ×
two allocation arrangements: **13,824 configurations**, each with two writes to
the same destination and exact whole-buffer/padding/bit/counter checks. Empty/error cases are
additional. macOS does not provide LSan here; Linux CI supplies its native checks.

A private byte-copy observer tests 36 positive cases and 36 overlapping rejects
before any copy. It observes explicit source copy events, not post-optimization
machine instructions or elapsed time. The old cell-only implementation fails
this regression as intended. Source/native equivalence, native refinement,
full allocation/backend-workspace attribution and controlled C-performance
acceptance remain separate obligations.
