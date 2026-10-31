# Prepared diagonal metric experiment

Run `python3 experiments/diagonal_metrics/run.py --prefix /path/to/openblas-0.3.34 --out /tmp/diagonal-results`.
The compiler is `cc` by default; select it explicitly with `--cc`.

This compares the actual C adapters with equivalent prepared C loops and the
same pinned sequential GEMM. Both sides use padded column-major caller storage,
the same coordinate order and default-overwrite policy, retain caller scratch,
and record output writes. C receives already realized double coefficients;
the adapter performs its required physical/bit preflight on immutable metadata.
The separate translation units use `-O3 -fno-lto` without fast-math. Every pair
checks exact output hashes (including scratch), writes, zero new arena data
allocations and zero copies. ASan/UBSan cases cover both operations/scalars.

This scope excludes the public source/Lean FFI boundary, setup/cleanup, metadata
construction, and total/backend allocation. It is diagnostic performance
evidence, not full-operation C parity or controlled-host acceptance. It does not
replace the source check/build/run tests, actual-checker proofs or exact emitted
schedule/counter regressions. All raw samples, command outputs, source hashes,
compiler/backend identity and host context are retained with each run.

The [initial run](results/2026-11-01-local/RESULTS.md) compares prepared C only.
The [matched-preflight run](results/2026-11-01-checked/RESULTS.md) additionally
checks identical applicable bounds/scalars/separation/backend/coefficients and
counter overflow before C writes. The [final run](results/2026-11-01-final/RESULTS.md)
measures explicit ordinary-column fast paths: representation and stride selection
move outside element loops, with the transposed path unchanged. The source hashes
identify each measured revision; none measures a later merge. All runs retain
substantial prepared-C gaps, particularly tiny calls and real pairings. The
intermediate 4,096-element real C case varies sharply versus both other runs;
the cause is unresolved and it is retained as unexplained run variability, not
evidence of a speedup.
These
gaps remain part of the [Stage 1 gate](../../docs/stage1-completion.md). This host
is shared and uncontrolled; no performance waiver or acceptance is implied.


The [validated run](results/2026-11-01-validated/RESULTS.md) retains complete
measured C/header/harness source snapshots as well as hashes. It checks every
post-timing coordinate against an independent bounded-integer reference in
addition to comparing output hashes. Earlier exploratory records retain hashes
and samples but not complete intermediate source snapshots; use the validated
record for reproducibility. None of these prepared C timings measures the later
linear first-touch Lean hex decoder; its metadata costs remain explicit in the
[metric guide](../../docs/diagonal-metrics.md).
