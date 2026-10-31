# Explicit tensor packing experiment

This optional experiment executes the actual public protocol-8 source for
`T[i,k,j] B[k,l] -> C[i,j,l]`: four explicit allocations, one `pack3` into
caller-owned scratch, then one overwrite `contract3` GEMM. It compares the
emitted program with a matched C algorithm using contiguous `x`-block copies
and the **same pinned sequential LP64 OpenBLAS 0.3.34 archive**. Native
compilation, passing checks, and smoke ratios do not establish C parity.

The C side uses the same arena allocation/fill/drop primitives and physical
layout preparation, then its own pack loop and direct CBLAS call. It does not
call `vstorage_pack3` or `vgemm_execute`. This controls allocator and setup
policy while exposing generated FFI and adapter overhead; it is not a claim
against every optimized C tensor implementation. Both sides use `-O3`, no LTO,
one backend thread, the same layouts, initialization, and explicit scratch.

## Run

Build the tools and the repository-pinned OpenBLAS prefix first (see
[the adapter instructions](../../docs/numerical-adapter.md)). Run from the
repository root:

```sh
cargo build --release --locked
lake -d lean-kernel build
python3 -m unittest discover -s experiments/tensor_packing -p 'test_*.py' -v
python3 experiments/tensor_packing/run.py \
  --prefix /path/to/pinned-openblas --output /tmp/tensor-smoke \
  --smoke --samples 3 --target-ms 0.1
```

The output directory must not exist. The harness uses existing compiler/kernel
binaries and never launches a shared kernel build. `--frontend` and `--kernel`
can select explicit binaries. Linux binds the launcher and its children to one
allowed CPU (`--cpu` overrides it). macOS is also supported, with no affinity
control and explicit `--no-leak-sanitizer` required because Apple ASan lacks
LSan. Linux should retain the default ASan/UBSan/LSan validation. No unavailable
toolchain fallback can turn a failed generated run into a successful result.

A reproducible exploratory full run uses twelve cases and eleven paired
samples with a 5 ms calibration target per batch:

```sh
python3 experiments/tensor_packing/run.py \
  --prefix /path/to/pinned-openblas --output /tmp/tensor-full \
  --samples 11 --target-ms 5
```

The dedicated Linux workflow runs four-case smoke validation on both `push`
and `pull_request` for changes to the harness and its selected native/checker
dependencies. Manual dispatch accepts `profile=smoke` (default) or `profile=full`;
the latter uses all twelve cases, eleven paired samples and the 5 ms target.
Both retain ASan/UBSan/LSan, one backend thread and a 45-minute job limit.
The target applies during calibration, not as a guarantee that later batches
remain above 5 ms; retain all samples when interpreting variability.

```sh
gh workflow run tensor-packing-experiment.yml --ref REVIEWED_REF -f profile=full
```

The workflow uploads two artifacts for 14 days: `tensor-packing-records-*`
contains raw rows, summaries, environment, commands, native validation, exact
source/wire/emission and wrappers; `tensor-packing-inspection-*` contains the
large symbol/disassembly listings whose hashes are in the command records.
The small record archive supports review without downloading disassemblies.
Preserve selected raw evidence in this repository before hosted retention ends.
Shared hosted runs remain exploratory and do not accept the controlled-host
performance gate or establish native refinement.

Cases cover `F64` and `Complex<F64>`, contiguous and offset/padded layouts,
and `(i,k,j,l)` equal to `(2,3,4,5)`, `(7,11,5,13)`, `(32,48,24,40)`.
Smoke selects only the first size. All axes are unequal. Constant fills plus
asymmetric complex patches (including an off-corner input value) keep source/checker work bounded as sizes
grow; timing repetition is a runtime loop, never an IR operation per element.
Empty/invalid dimension semantics belong to checker/native regressions and
are not throughput cases here.

## Timed scopes and costs

| Scope | Included in reported time | Outside reported time |
|---|---|---|
| `lifecycle` | Emitted allocation, sentinel and operand initialization, pack, GEMM, drops, arena cleanup, Lean FFI | Compiler, process startup, common warmup, terminal pure-result printing |
| `reused_buffers` | Repeated pack + GEMM, both generated FFI calls and physical preflights | One allocation/setup and final validation/cleanup |
| `pack_adapter` | Pack API and physical preflight, including exact copy/write accounting | Lean FFI, GEMM, setup, cleanup |
| `blas_kernel` | Actual pinned CBLAS call | Both FFI calls, pack, physical preflight, setup, cleanup |

The last two scopes still execute the complete pack + GEMM schedule and time
only the named region. Their `timed_*` counters describe the **whole repeated
schedule**, not only the timed region. Per-call clock instrumentation perturbs
these diagnostics, especially tiny cases. It is disabled in the two primary
scopes. `CLOCK_MONOTONIC_RAW` is used where available, with a monotonic fallback;
zero-duration verification/warmup diagnostics are permitted, and calibration
increases repetitions for measurement. No timer overhead is subtracted.

Let `w` be the scalar width, `P=i*k*j*w`, `O=i*j*l*w`, and `S` the total
capacity in bytes of all four buffers. Each operation copies exactly `P` bytes
and writes `P+O` bytes after setup. Setup writes `S` sentinel bytes, all logical
input bytes, and four patch scalars. A lifecycle repetition has four data
allocations/frees; reused buffers have zero timed data allocations/frees.
Peak data bytes are exactly `S`, including scratch and padding. Metadata
allocations/peak bytes, total/timed writes/copies, drops, and zero final live
bytes are checked on both sides, then paired records must agree exactly.
The pack is never hidden as an untimed one-time preprocessing step.

## Acceptance and diagnostics

Each case runs the real frontend check, canonical build and executable,
independent Lean wire check/emit, then compiles a wrapper around that **actual
emitted source**. In `lifecycle`, the wrapper removes only terminal printing
and preserves the whole resource schedule and `try/finally`. In the three
reused scopes, it explicitly hoists the emitted setup/cleanup around a runtime
loop of the emitted pack + GEMM instructions. This hoisting is an experimental
reuse measurement, not execution of an unchanged single-shot public schedule.
Instruction operands and cleanup remain exact; the wrapper fails closed if
codegen's reviewed straight-line shape changes. Private runtime copies provide timing,
counters, and inspection; production files are untouched. Both sides execute
the same untimed generated warmup in each fresh process.

The oracle checks every original/right element, every packed coordinate
`packed[x+i*y,z] = T[x,z+k*y]`, every output coordinate against a direct
contraction over original coordinates, and every padding cell. A mutation regression requires every fixture to
distinguish the correct packing from simply copying the original logical flat
order; first/last-only patches would miss this error. Native selftests also
perform that wrong copy without damaging padding, run GEMM on it, and require
both packed-coordinate and resulting-output oracles to reject it before
restoring the valid operation. Input, pack,
and padding checks are bit exact; arithmetic output has an explicit
`32*epsilon*(k+1)*max(1,abs(expected))` tolerance. Hashes must also agree exactly
between the two implementations. Real/imaginary multiplication is explicit;
there is no implicit conjugation. Deliberate corruption of all four logical
buffers and padded prefixes must be detected. Invalid pack shape/alias and
aliased GEMM attempts must reject without changing valid data/copy/write
counters. ASan/UBSan (and Linux LSan by default) validate the standalone native
adapter and C baseline; these sanitizers do **not** instrument the complete
Lean executable or the prebuilt OpenBLAS archive.

Correctness checks run outside measurement batches, including before/after
paired sampling; reused buffers are also validated after each batch. Lifecycle
measurement batches consume the first output word at drop and use the
separate verification batches for full output validation. Case order is
seeded; paired implementation order alternates. Raw calibration/warmup and
measurement rows, exact source/wire/emission, canonical/wrapped programs,
compile/check phase times, toolchain/host/backend provenance, hashes, and
native sanitizer records remain in the output directory. Large disassembly
is stored once, with path/size/hash in bounded command logs. Interrupted runs
retain the last atomic status/command snapshot and flushed raw rows.

`summary.json`/`summary.md` use the storage-copy experiment's median, IQR, MAD,
paired ratios/deltas and paired bootstrap interval. A bootstrap interval
covers within-run sampling only, not host/process uncertainty or a performance
acceptance gate. `process_maxrss_kib` is normalized to KiB on both platforms;
on Linux it may retain launcher pre-exec footprint and is **not** isolated
executable heap or BLAS memory. Exact arena counters are the resource evidence.
OpenBLAS private packing/allocations, stack/runtime heap, cache pressure and
host activity are not separately instrumented. Full results are exploratory
unless collected and assessed under the controlled-host completion gate.

The first strengthened all-size validation is recorded in
[the macOS validation record](results/2026-10-31-macos/RESULTS.md).
