# Tensor packing: strengthened fixture validation

Status: **actual generated execution and matched output/cost contracts passed**
on 2026-10-31. This is a short validation run over all twelve cases, **not** the
11-pair/5 ms full measurement profile or controlled-host C-parity acceptance.
The performance completion gate remains open.

Command, from the tensor implementation worktree:

```sh
python3 experiments/tensor_packing/run.py \
  --prefix /private/tmp/vastitas-openblas-verified \
  --output /private/tmp/vastitas-tensor-final-validation \
  --frontend target/debug/vastitas \
  --samples 3 --target-ms 0.1 --no-leak-sanitizer
```

The debug frontend affects compilation/check timing; generated Lean/native code
and the C baseline use `-O3`, without LTO. Host: macOS 27.2 arm64, Apple Clang
21.0.0, pinned Lean 4.35.0, sequential LP64 OpenBLAS 0.3.34 (`VORTEXM4`, one
thread). CPU brand query was unavailable and is retained as a failed environment
probe. No CPU affinity or host isolation was applied. Apple ASan lacks LSan;
leak detection was explicitly disabled, while ASan/UBSan passed. Arena final
live bytes and exact frees are checked separately and do not establish absence
of every runtime/backend heap leak.

The final run took 91.8 seconds and completed:

- 12 public checks, canonical builds/executions, independent Lean checks/emits,
  and wrappers compiled from their actual emitted source.
- 24 standalone native records: optimized and ASan/UBSan validation for every
  real/complex, contiguous/padded, tiny/small/bulk case.
- 840 raw rows, including 288 measurement rows (144 measured pairs), and 48
  case/scope summaries. Every paired output/cost contract passed.
- An independent recomputation of dimension/capacity cost equations for all
  840 rows: four allocations/frees per lifecycle, zero timed allocations/frees
  with reused buffers, exact pack/write bytes, and zero final live bytes.
- 1,210 commands in a 1,120,556-byte log. Disassembly stayed in separate files;
  archived command records retain their byte counts and hashes.

The data fixture was strengthened during independent review. An earlier version
changed only the first and last tensor entries; those entries were invariant
under a wrong flat copy. Those preliminary runs are **excluded** from this
record. The final run uses an off-corner `z=1,y=0` value, and a regression proves
that every one of the twelve fixtures distinguishes the actual pack from an
unchanged logical flat copy.

After the final all-size run, the standalone selftest gained a permanent native
flat-copy mutation: it copies logical flat order without touching padding,
runs GEMM, requires both packed-coordinate and resulting-output oracles to
reject it, and restores the valid operation. That test passed in optimized and
ASan/UBSan runs for all four real/complex × contiguous/padded smoke cases.
Its exact commands/source/records are archived under `native-flat-copy-regression`.
The change is inside `BENCH_STANDALONE`; it does not change the measured generated
wrapper. Independently compiled wrong-pack implementations for padded real and
complex cases preserved exact write/copy accounting and still failed coordinate
verification, aborting as expected; see `independent-flat-copy-mutant`.

Six Python harness regressions also passed:

```sh
python3 -m unittest discover -s experiments/tensor_packing -p 'test_*.py' -v
```

[Raw rows](raw.csv.gz), [summary data](summary.json.gz), and
[summary table](summary.md) preserve the short timing observations. These ratios
include timer effects and uncontrolled host activity, and are not an acceptance
claim. In particular, diagnostic `pack_adapter`/`blas_kernel` times exclude the
other operation while their counters describe the whole repeated schedule.
The full lifecycle includes setup/cleanup; reuse explicitly hoists those steps
around repeated emitted pack/GEMM calls. Launcher-inclusive RSS is not isolated
runtime heap or BLAS workspace.

[Evidence archive](evidence.tar.gz) contains exact source snapshots, fixture
packages/wires, canonical emitted source, wrapped source, native and mutation
validation, command logs and compile timings. Executable/disassembly binaries
are omitted; [binary hashes](binary-manifest.json) and inspection-file hashes
remain. [Environment](environment.json) records compiler/kernel/backend hashes,
working-tree state and toolchain details. [SHA256SUMS](SHA256SUMS) covers the
stored evidence. This run used the tensor feature working tree before its
combined commit; the captured source and binary hashes identify what ran.
