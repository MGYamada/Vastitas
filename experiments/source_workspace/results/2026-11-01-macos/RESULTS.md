# macOS checked-source workspace observation

Measured source and backend calibration both use clean commit
`605a5a7c82697bd53241983e8a42c03a68fd372a`. This is a local arm64 macOS 27.2
observation with Apple clang 21.0.0, Lean 4.35.0 and pinned sequential LP64
OpenBLAS 0.3.34 (`VORTEXM4`, upstream `NO_WARMUP`). No operation timings or
controlled-host acceptance are claimed.

The [archive manifest](artifact-manifest.json) binds `evidence.zip` (3,668,155 bytes,
1,784 members), SHA-256
`e2db3ba1b55a2c5a77941b5a9820b26c6c06f89b22ba7b4bfbfea903a7d2a129`.
All 60 source snapshots and the nested calibration's 16 source snapshots were
independently compared with that Git commit. The source runner records 559
commands; the nested backend calibration retains its separate command log and
75 stock/diagnostic pairs. The exact kernel wire, returned Lean, emitted C,
private runtime, raw outputs and executable fingerprints remain available.
Large executable files and Lake caches are explicitly omitted.

| Observed boundary | Result |
| --- | --- |
| Public source | 12 tiny/small/bulk × real/complex × padding cases; 24 unchanged-stock check/build/executions |
| Matched observed operations | 288 normal records: generated/C × stock/diagnostic × lifecycle/reuse × batches 1/2/17 |
| Propagated native failure | 24 separately checked wrong-expectation variants; all release six data allocations and the arena |
| Actual CBLAS calls | 4,512 total; exact scalar, shape, leading dimensions and coefficient bits agree |
| Diagnostic source processes | 156; 2,256 pool borrows and 2,256 returns, assigned to their actual CBLAS intervals |
| Backend backing | Each process maps one 32 MiB buffer in its cold source operation; it is retained with zero outstanding loans until explicit quit |
| Reuse batch of 17 | 34 borrows/returns, zero additional backing events; generated/C backend phase counts and peaks agree |
| Shutdown | 156 maps and 156 unmaps; all 156 complete shutdown pairs release the retained backing |
| Explicit native data/metadata | Peak data ranges from 1,624 to 2,825,248 bytes across fixtures; arena metadata peak is 280 bytes; generated/C counters agree |
| Selected Lean objects | Generated warm lifecycle batch allocates `56N+64` bytes; reuse allocates 64 bytes. Tracked peak is 88 bytes, including the 16-byte persistent Unit result; `finally` fallback remains charged |
| Observer objects | Backend static objects: 163,869 bytes; call bridge: 24,596 bytes. These exclude linker padding, stack, code, strings and reporting allocations |

The C comparison runs in the same Lean-hosted fixture and performs the same cold
generated operation first. It does not establish standalone C startup/heap
equivalence. Stock backend intervals are null, never an observation of zero
workspace. Mapping capacity is not RSS or actual packed bytes. An empty interval
would mean only that these hooks observed no event.

All operation clocks are disabled. The inherited `timed_*` fields designate the
selected run scope; `process_maxrss_kib` is an unisolated diagnostic excluded from
cost comparison. General Lean/allocator traffic, backend static metadata outside
the observer, other backend files, actual backend packing/copy traffic and
meaningful per-operation resident peaks remain unmeasured. The largest fixture
is not representative memory-bound performance evidence. These data do not meet
the controlled-host, tiny-call budget or total-cost completion gates.

Run `python3 experiments/source_workspace/verify.py experiments/source_workspace/results/2026-11-01-macos/evidence.zip`
from the repository root to replay without executing archived code. The later
review-strengthened verifier accepts these unchanged records and checks all
surrounding selected-object phases and generated/C backend cost equality.
Hashes establish retained-byte integrity, not authenticity or native refinement.
