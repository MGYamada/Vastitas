# Linux workspace and backing observation

Measured clean revision: `cc42822f120c8792e7fa0747b509282dcd934dde`.
The successful [push workflow](https://github.com/MGYamada/Vastitas/actions/runs/41270586125),
[Linux job](https://github.com/MGYamada/Vastitas/actions/runs/41270586125/job/124742364265)
produced artifact `13069615474`. Its complete ZIP was downloaded, its GitHub digest
checked, and its events independently replayed locally. All 16 source snapshots
were also checked against the measured Git commit. This revision precedes the
publication commit and explicit 64-bit promotion of bounded fixture-size
arithmetic; those later sources are not relabeled as measured here.

The retained run contains **150 fresh-process executions / 75 stock–diagnostic
pairs**: three repetitions of calibration plus 24 real/complex N/T/C adapter
cases. Independent coordinate and padding checks, stock/diagnostic agreement,
all 75 lifetime replays and the full inventory pass.

Host: x86_64, Linux 7.0.0-1017-azure, glibc 2.43, GCC 15.2.0. The build explicitly
selects `TARGET=HASWELL`; the backend reports
`OpenBLAS 0.3.34 NO_LAPACK NO_LAPACKE NO_AFFINITY USE_LOCKING HASWELL SINGLE_THREADED`.
The actual physical CPU model was not recorded and must not be inferred from
the compilation target. Stock and diagnostic inventories contain 2,483 objects;
only `driver/others/memory.o` changes. This is a shared hosted runner and a rebuilt
diagnostic backend, with no timing or controlled-host claim.

| Observed channel | Calibration process | Each nonempty GEMM process |
|---|---|---|
| Pool buffer capacity | 134,217,728 bytes per buffer | 134,217,728 bytes |
| Peak simultaneous borrowed capacity | 268,435,456 bytes (two buffers) | 134,217,728 bytes (one buffer) |
| mmap capacity retained after all returns | 268,435,456 bytes | 134,217,728 bytes |
| Direct/no-lock malloc request | 134,221,824 bytes, then freed | None in this observed file |
| Final backing after explicit quit | Zero | Zero |
| Observer mutable storage | 163,869 bytes | 163,869 bytes |

Each of the 54 nonempty diagnostic GEMM processes maps one buffer on its first
call. The repeated overwrite and accumulation reuse that mapping. Each completed
call has zero active loans while backing stays retained until explicit quit.
The 18 empty-case processes have no backing or loan event. Rejected preflight
has no backend event and leaves the checked inputs/output/padding unchanged.
Output checksums canonicalize only computed zero signs.

Across all 75 diagnostic processes: 60 mmap requests/unmaps; 171 pooled
borrows/returns; three direct borrows/returns and three malloc/free pairs;
75 shutdown begin/end pairs and 534 phase markers. No allocation failure is
recorded. These are population totals, not a single program's cost. The summary
groups only identical observations and retains every case and repetition.

The actual memory compile command includes upstream `-DNO_WARMUP`; there are no
phase-0 allocation or partial-unmap events. The observer is positioned to capture
constructor calls, but this record does not calibrate a warmup-enabled build.
The partial-unmap replayer is covered by synthetic mutation tests separately.
Although `SMALL_MATRIX_OPT` is enabled, all observed nonempty cases borrow;
other inputs/backends are not assigned that same behavior without observation.

The 128 MiB pool capacity is a reserved virtual mapping request, **not a claim of
128 MiB RSS or packed matrix data**. Borrowed capacity overlaps backing and
cannot be added to it. malloc accounting uses request sizes, not usable size or
allocator backing. General Lean allocations, other backend files, stack/local
packing, generated-source lifecycles and full process peaks remain unmeasured.

```sh
python3 experiments/openblas_workspace/verify.py \
  experiments/openblas_workspace/results/2026-11-01-linux/evidence.zip
```

The [manifest](artifact-manifest.json) retains the workflow/job/artifact IDs,
518 members, 166 commands, 711,111 ZIP bytes and SHA-256
`bf34e83fc2a352bc1fafd98d40b6f052a0ac039510d5b27b9a84268b829b18b2`.
[`summary.json`](summary.json) is reproduced by `--summary`. The distinct
[macOS record](../2026-11-01-macos/RESULTS.md) has a 32 MiB buffer; that is a
different compiled backend, not a before/after optimization.

The [total-cost and timing acceptance gates](../../../../docs/stage1-completion.md)
remain open. Neither a successful diagnostic nor ordinary BLAS execution
establishes Fast like C.
