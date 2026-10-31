# 2026-10-31: generated public GEMM smoke validated

The Linux smoke run passed the real public checker, canonical executable,
generated measurement wrapper, and paired output/cost contracts for all 16
tiny/small cases. **This is execution validation, not performance acceptance.**
The shared hosted runner, three pairs per scope and 0.1 ms calibration target
do not establish C parity, #222, native refinement or Stage 1 completion.
No speed ratios are reported here. The
[original unavailable-toolchain record](../2026-10-31-linux-unmeasured/RESULTS.md)
remains unchanged and describes a separate attempt.

## Exact run and command

- PR head: `e77243bcc0eb97582c736a28a6e774ab802a1251`.
- Actual PR merge checkout recorded by the harness:
  `4ff6a64af82fa95ba8cf0ccde76e5c9452c85d59`.
- [Successful PR job](https://github.com/MGYamada/Vastitas/actions/runs/41197200169/job/124525657978):
  5 min 48 sec including setup; the harness ran from 11:34:31 to 11:37:04 UTC.
- [Successful push job](https://github.com/MGYamada/Vastitas/actions/runs/41197196210/job/124525647349):
  6 min 44 sec including setup.
- Lean 4.35.0, GCC 15.2.0, Linux x86-64/glibc 2.43; sequential LP64
  OpenBLAS 0.3.34 built for HASWELL with all thread variables set to one.

After the workflow built the independent kernel, pinned OpenBLAS and release
frontend, it ran:

```sh
python3 experiments/public_gemm/test_harness.py
python3 experiments/public_gemm/run.py \
  --prefix "$RUNNER_TEMP/gemm-openblas" \
  --output "$RUNNER_TEMP/public-gemm-smoke" \
  --smoke --samples 3 --target-ms 0.1
```

Neither `--allow-unavailable` nor `--no-leak-sanitizer` was used.

## Inspected validation evidence

| Check | Result |
| --- | --- |
| Harness regressions | 5 passed, including bounded logging of a 3 MiB inspection output |
| Native C-adapter/direct-CBLAS validation | 16 cases passed |
| Native ASan/UBSan/LSan validation | 16 cases passed; fatal diagnostics and LSan enabled |
| Normal `vastitas check`, `vastitas build`, unmodified executable | 16 of each passed; each executable printed `0` |
| Independent kernel `check` and `emit` | 16 of each passed; exact response/emitted source retained |
| Generated wrapper compilation and execution | All 16 passed in lifecycle, prepared-call and BLAS-kernel scopes |
| Retained raw rows | 908: 192 warmup, 428 calibration, 288 measurement |
| Complete generated/C pairs | 454; every output/checksum/cost field agreed except intentionally excluded time and RSS |
| Separate untimed runtime validation | 192 process invocations passed |
| Inspection files | All 48 retained paths, byte counts and SHA-256 hashes independently checked |

All recorded arena live-byte counts were zero after cleanup, allocations equaled
frees, and copied bytes were zero. Prepared scopes allocated/copied zero matrix
bytes in their measured window. Peak matrix capacity ranged from 208 to 14,960
bytes, including padding. These are arena facts, not total process allocation or
BLAS-private packing measurements. The larger bulk cases were not run in this
smoke; their original native-only validation remains separately recorded.

The [PR artifact](https://github.com/MGYamada/Vastitas/actions/runs/41197200169/artifacts/13041114525)
contains the source packages, checker responses, emitted source, wrappers,
command/compile records, native/sanitizer diagnostics, raw pairs and 48 scope
summaries. Its ZIP size is 80,296,753 bytes and SHA-256 is
`9d45ce4e916de77d3aefaf82c41f04d73c04c3a5e391c8459fa599efea50563c`.
The workflow retains it for 14 days, through 2026-11-14. This repository stores
this aggregate validation record, not a durable copy of the entire archive.

## Preserved first hosted failure and limitations

The [first PR smoke](https://github.com/MGYamada/Vastitas/actions/runs/41193852109/job/124515938965)
at head `2f696daa2f84a7bfc3bcd731a93b64a33fecd097` timed out after 45 minutes.
Its artifact `13041186891` contained a 349,044,736-byte `commands.json`, truncated
inside an inspection-output string when the job was canceled. The harness had
been copying complete disassemblies into every subsequent JSON snapshot. The
partial numerical rows from that attempt are not a completed measurement run.

The fix retains each large inspection output once, records its path/size/hash,
and atomically replaces diagnostic JSON snapshots. It kept all 16 cases, all
three scopes, sanitizer settings and the 45-minute timeout. The successful
run's complete `commands.json` was 1,185,678 bytes, with no unexpected command
failures.

RSS remains diagnostic only. Before the fix, reported `ru_maxrss` grew alongside
the Python command history. Linux preserves resource usage across `execve`, so a
fresh subprocess can retain a launcher's pre-exec footprint. The successful
run's 62,520–65,464 KiB range does not establish isolated executable/Lean/BLAS
heap consumption. See the [method and RSS boundary](../../README.md).
