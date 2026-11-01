# Large-output checked source costs — Linux

This complete streaming profile measures clean
`ceff5840e4fd1dbdf0e4ab012d2fd52cab062e7d`. The same public contraction-tree source,
returned instructions, coordinate oracle and matched C work now cover 128 MiB
real and 256 MiB complex outputs. This is a cost observation, not a timing or
memory-bandwidth acceptance claim.

| Provenance | Value |
| --- | --- |
| Host | Linux 7.0.0-1017-azure x86_64, glibc 2.43, `/usr/bin/cc`; shared GitHub runner |
| Lean | Installed 4.35.0 and private calibrated rebuilt-zero / `MI_STAT=2` archives |
| Lean calibration | Clean `ceff5840e4fd1dbdf0e4ab012d2fd52cab062e7d`, retained in the archive |
| Backend calibration | Clean `ceff5840e4fd1dbdf0e4ab012d2fd52cab062e7d`, sequential LP64 OpenBLAS 0.3.34, HASWELL |
| Source inputs | All 81 repository snapshots independently matched to the measured Git revision |
| Compact archive | [evidence.zip](evidence.zip), 8,215 members, 34,880,910 bytes |
| SHA-256 | `6f5048e98edc427b3045dddaf2439496d526a3b79fb4348eedc06d52aa3e337b` |
| Export receipts | [artifact manifest](artifact-manifest.json), [GitHub provenance](github-artifact.json) |
| Source CI | [Streaming run 41310354369](https://github.com/MGYamada/Vastitas/actions/runs/41310354369/job/124859243216) |

## Complete profile

The fixed `(i,k,j,a,b) = (512,2,2,64,512)` dimensions use small reduction axes
and a large destination. Real/complex and padded/unpadded layouts cross both
backends and all three Lean variants, with lifecycle and caller-buffer reuse
batches of **1 and 2**. This separate profile does not replace the standard
1/2/17 cases or relabel a debug run as complete.

All **24 canonical public check/build/executions, 192 normal observations and
24 checked failure cleanups** passed. The 216 processes retain **1,056 actual
CBLAS calls and 2,160 allocator snapshots**. All 24 observed source packing
contracts passed 96 additional plain/sanitized stock/diagnostic footprint
executions. The largest observed packing-event count is 825, below the unchanged
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
and twice those amounts for complex. The observed copy-call counts are 6 / 86
and 18 / 257 respectively. These are logical payloads, not hardware traffic.

Diagnostic lifecycle batches observe 5 / 7 normal allocations and 104 / 144
binned bytes. Reuse observes three / 64 per batch; matched C's run phase observes
zero; checked failure observes seven / 184. No normal count/byte remains
unattributed in the observed diagnostic phases. Other allocators, startup and
stock total-heap counts are not supplied by these overlapping channels.

## Validation and remaining acceptance

The CI runner, archive replay and all 69 replay/mutation tests passed with this
record selected. Independent local ZIP replay reproduced its manifest exactly;
both outer/inner digests and all 81 Git snapshots passed. Its source inputs match
the [macOS record](../2026-11-01-macos-streaming/RESULTS.md), while the separately
calibrated backend retains different packing call counts and pool capacity. Larger
output size does not establish a cache-miss rate, DRAM traffic or a bottleneck;
operation clocks remain disabled. The 128 MiB retained backend mapping is virtual
capacity, not RSS or operation peak memory. The libraries' complete calibration
records are preserved alongside the source observations.

Requested-byte/general peak accounting, other source profiles and shortcut
internals remain separate. A predeclared tiny-call budget and controlled-host
equivalent-C timings are still required by the
[Stage 1 completion gate](../../../../docs/stage1-completion.md). Neither source
execution nor archive integrity proves native refinement.

Publication validation passed all 71 source replay/mutation tests with the Linux
streaming record selected, including explicit replay of both post-cleanup and
both streaming exports. This later verification preserves the original measured
heads, source snapshots and raw observations.
