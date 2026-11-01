# Large-output checked source costs — macOS

This complete streaming profile measures clean
`ceff5840e4fd1dbdf0e4ab012d2fd52cab062e7d`. The same public contraction-tree source,
returned instructions, coordinate oracle and matched C work now cover 128 MiB
real and 256 MiB complex outputs. This is a cost observation, not a timing or
memory-bandwidth acceptance claim.

| Provenance | Value |
| --- | --- |
| Host | Local macOS 27.2 arm64, `/usr/bin/cc`; no fixed CPU or controlled-host claim |
| Lean | Installed 4.35.0 and private calibrated rebuilt-zero / `MI_STAT=2` archives |
| Lean calibration | Clean `54531c11b2843a0d3d7565b71e7463e4387b8c03`, retained in the archive |
| Backend calibration | Clean `db62d224837031f1a8b3e05e6ca4756325716a04`, pinned sequential LP64 OpenBLAS 0.3.34 |
| Source inputs | All 81 repository snapshots independently matched to the measured Git revision |
| Compact archive | [evidence.zip](evidence.zip), 8,237 members, 25,258,478 bytes |
| SHA-256 | `251a8a27324ac76f58035d721b9ecd0668bec55a4c032133b36c3a85d2f3e9a3` |
| Export receipt | [artifact-manifest.json](artifact-manifest.json) |

## Complete profile

The fixed `(i,k,j,a,b) = (512,2,2,64,512)` dimensions use small reduction axes
and a large destination. Real/complex and padded/unpadded layouts cross both
backends and all three Lean variants, with lifecycle and caller-buffer reuse
batches of **1 and 2**. This separate profile does not replace the standard
1/2/17 cases or relabel a debug run as complete.

All **24 canonical public check/build/executions, 192 normal observations and
24 checked failure cleanups** passed. The 216 processes retain **1,056 actual
CBLAS calls and 2,160 allocator snapshots**. All 20 observed source packing
contracts passed 80 additional plain/sanitized stock/diagnostic footprint
executions. The largest observed packing-event count is 942, below the unchanged
16,384-entry capacity. No calibrator stride limit or observer bound was relaxed.

| Case | Logical output bytes | Peak live arena data | Explicit packing bytes per operation |
| --- | ---: | ---: | ---: |
| Real, contiguous | 134,217,728 | 135,291,904 | 540,672 |
| Real, padded | 134,217,728 | 135,342,096 | 540,672 |
| Complex, contiguous | 268,435,456 | 270,583,808 | 1,081,344 |
| Complex, padded | 268,435,456 | 270,684,192 | 1,081,344 |

Every output, surviving scratch cell and padding cell is checked. Initial fills,
caller-owned scratch and explicit packing stay charged; packing reuses the
declared scratch buffer. The actual two GEMMs use packed backend routes. Their A/B
logical copy payloads are 16,384 / 1,024 then 524,288 / 8,192 bytes for real,
and twice those amounts for complex. The observed copy-call counts are 10 / 172
and 14 / 300 respectively. These are logical payloads, not hardware traffic.

Diagnostic lifecycle batches observe 5 / 7 normal allocations and 104 / 144
binned bytes. Reuse observes three / 64 per batch; matched C's run phase observes
zero; checked failure observes seven / 184. No normal count/byte remains
unattributed in the observed diagnostic phases. Other allocators, startup and
stock total-heap counts are not supplied by these overlapping channels.

## Validation and remaining acceptance

The full runner, independent directory/ZIP replay and all 69 replay/mutation
tests passed with this record selected. All 81 snapshots match Git. Larger
output size does not establish a cache-miss rate, DRAM traffic or a bottleneck;
operation clocks remain disabled. The 32 MiB retained backend mapping is virtual
capacity, not RSS or operation peak memory. The calibrated libraries retain
their own revisions rather than inheriting the source record's commit.

Requested-byte/general peak accounting, other source profiles and shortcut
internals remain separate. A predeclared tiny-call budget and controlled-host
equivalent-C timings are still required by the
[Stage 1 completion gate](../../../../docs/stage1-completion.md). Neither source
execution nor archive integrity proves native refinement.

Publication validation passed all 71 source replay/mutation tests with the Linux
streaming record selected, including explicit replay of both post-cleanup and
both streaming exports. This later verification preserves the original measured
heads, source snapshots and raw observations.
