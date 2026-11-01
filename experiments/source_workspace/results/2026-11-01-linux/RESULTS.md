# Linux checked-source workspace observation

Measured source and backend calibration both use clean commit
`605a5a7c82697bd53241983e8a42c03a68fd372a` in
[push workflow 41274204681](https://github.com/MGYamada/Vastitas/actions/runs/41274204681),
[Linux job 124752952080](https://github.com/MGYamada/Vastitas/actions/runs/41274204681/job/124752952080).
Artifact `source-workspace-ubuntu-latest-push` has ID `13070259932`; the downloaded
outer ZIP hash is `f8596917957d7924f0b8f0b9702190312487392cfe968a9281c79316f8ae75d4`.

The host reports x86_64 Linux 7.0.0-1017-azure, glibc 2.43 and GCC 15.2.0.
Lean is 4.35.0; pinned sequential LP64 OpenBLAS 0.3.34 targets `HASWELL` with
upstream `NO_WARMUP`. The actual CPU model is not captured; the compile target
does not identify it. This shared GitHub runner is not a controlled performance host.

The [archive manifest](artifact-manifest.json) binds `evidence.zip` (4,258,277 bytes,
1,784 members), SHA-256
`de58f3b4b22dddcf1359aebf665c4518d3c2d467e6fc11dee86b10a497ebcdd0`.
All 60 source snapshots and the nested calibration's 16 source snapshots were
independently compared with the measured Git commit after download. The source
runner retains 559 commands, exact checked wire/returned Lean/emitted C/private
native sources, all raw observations and executable fingerprints. The nested
75-pair calibration retains unchanged calculation-object hashes. Large Lean
executables and Lake caches are excluded explicitly.

| Observed boundary | Result |
| --- | --- |
| Public source | All 12 cases, 24 unchanged-stock check/build/executions |
| Normal/failure observations | 288 matched source/C stock/diagnostic lifecycle/reuse records, plus 24 successful propagated-failure cleanups |
| Actual CBLAS calls | 4,512 total; exact scalar, shape, leading dimensions and coefficients agree |
| Diagnostic source processes | 156; 2,256 pool borrows and 2,256 returns, each attributed to an actual call |
| Backend backing | One 128 MiB mapping per process in the cold source operation; retained with zero outstanding loans until quit |
| Reuse batch of 17 | 34 borrows/returns without additional backing events; generated/C backend phase counts and peaks agree |
| Shutdown | 156 maps/unmaps and 156 complete shutdown pairs; no observed backing or loans remain |
| Explicit arena costs | 1,624–2,825,248 peak data bytes by case, 280 metadata bytes; matched C agrees |
| Selected Lean objects | Generated warm lifecycle bytes `56N+64`, reuse 64; peak 88, including 16 retained Unit bytes and charged caller fallback |
| Explicit observer static sizes | Backend 163,869 bytes and call bridge 24,596 bytes; no alignment/stack/code/report-allocation claim |

The [macOS record](../2026-11-01-macos/RESULTS.md) observes a different 32 MiB
backend pool configuration. These capacities are virtual mapping amounts, not
actual packing traffic, residency or a cross-host performance comparison.
Both records have a cold generated operation even in C comparison processes.
Stock backend event intervals remain unobserved/null. General Lean/allocator
traffic, backend static metadata/other files, actual packing/copy bytes and
meaningful per-operation peak memory remain outstanding.

Operation clocks are disabled. The inherited `timed_*` labels identify the run
scope only, and `process_maxrss_kib` is excluded from cost equality. This fixed
fixture's largest working set is not memory-bound performance acceptance. No
controlled-host, tiny-call budget, total-cost or native-refinement completion
claim follows.

Run `python3 experiments/source_workspace/verify.py experiments/source_workspace/results/2026-11-01-linux/evidence.zip`
to replay the archived bytes without executing them. Later verifier mutation
regressions strengthen surrounding-phase accounting and generated/C backend cost
equality while preserving the original measured revision and raw bytes.
