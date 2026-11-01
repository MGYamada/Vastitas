# Checked source allocator phases — macOS

Full diagnostic record from clean
`f0e0c55d79978d68021ba0ee0831916d1153606d`, submitted in
[PR #366](https://github.com/MGYamada/Vastitas/pull/366).
This is allocation/cost evidence, not timing acceptance or native refinement.

| Provenance | Value |
| --- | --- |
| Host | macOS 27.2, arm64; `/usr/bin/cc`; no isolated CPU or controlled-host claim |
| Lean | Installed 4.35.0; stock plus private rebuilt-zero / `MI_STAT=2` runtime archives |
| Lean calibration | Clean `54531c11b2843a0d3d7565b71e7463e4387b8c03`; complete nine-process / 162-snapshot record retained inside this archive |
| Backend calibration | Clean `605a5a7c82697bd53241983e8a42c03a68fd372a`; complete paired OpenBLAS 0.3.34 calibration retained; sequential LP64, VORTEXM4, `NO_WARMUP` |
| Source inputs | 66 repository snapshots, independently matched to the measured Git revision |
| Source commands | 1,663, including exact kernel-stdin hashes, context and raw observations |
| Compact archive | [evidence.zip](evidence.zip), 4,666 members, 41,924,992 bytes |
| SHA-256 | `1a5230c1a895c59a44070aa20a001d745164a16efa32e301a089dcedd5ce7efd` |
| Export manifest | [artifact-manifest.json](artifact-manifest.json) |

The older calibrations are reused only after matching every selected archive,
required observer/header and installed toolchain fingerprint. Their measured
revisions remain distinct from the source experiment's revision. Canonical public
executables always use stock Lean and stock BLAS. Only private observation
executables select the calibrated archives; complete linker maps bind each one.
No installed toolchain or production runtime is modified.

## Coverage and observations

All twelve tiny/small/bulk, real/complex, padded/unpadded cases cross three Lean
runtimes with two backends. There are **864 normal executions, 72 checked failure
cleanups and 72 canonical public check/build/executions**. The 936 observation
processes produce 9,360 allocator snapshots, including an immediate empty repeat
at each boundary. The repeats agree. The 312 `MI_STAT=2` processes have calibrated
normal count/binned-byte deltas; the other 624 retain raw values but have null
summaries for unsupported normal-allocation counts.

For every tested case and both backends, the measured run phase is:

| Operation | Repetitions | Normal allocations | Binned bytes | Current-byte change |
| --- | ---: | ---: | ---: | ---: |
| Generated lifecycle | 1 | 6 | 120 | 0 |
| Generated lifecycle | 2 | 9 | 176 | 0 |
| Generated lifecycle | 17 | 54 | 1,016 | 0 |
| Generated caller-buffer reuse | 1 / 2 / 17 | 3 | 64 | 0 |
| Matched C, either scope | 1 / 2 / 17 | 0 | 0 | 0 |
| Checked failure and cleanup | 1 | 7 | 184 | 0 |

The lifecycle observations agree with the existing `3N+3` selected objects /
`56N+64` bytes for these three batch sizes. The prepared/reuse observation includes
fixed wrapper/control objects; it is not a per-call 64-byte cost. The C comparator
runs inside the same Lean-hosted fixture, after the same cold generated operation;
it is not standalone C process accounting.

Cold execution allocates five normal objects / 88 binned bytes and leaves the
16-byte persistent Unit result. Final recorded normal current is 16 in all 312
diagnostic processes. Setup includes release of pre-baseline command arguments;
negative current-byte changes are retained, not interpreted as negative allocation.

The failure run's five selected objects account for 88 bytes. Inspection of the
actual error payload identifies two further objects: a 16-byte `IO.Error` and a
string with 76 requested / 80 usable bytes, including its 44-byte UTF-8 payload
and terminator. Thus the extra **two allocations / 96 binned bytes** explain the
full 7 / 184 observation. The requested-byte counter changes by 180, not 184.
The original selected-object audit did not include those two payload objects.

Across all four observed phases and 312 diagnostic processes, no further normal
allocation is unattributed, and no huge allocation is observed. This is scoped
empirical evidence for these fixtures. Selected-site, allocator, arena and backend
channels overlap and must not be added as independent costs.

The 13,536 actual CBLAS calls retain exact dimensions, layouts, coefficients and
event intervals. The 468 backend-diagnostic processes observe 6,768 pool borrows
and matching returns, plus one 32 MiB mapping per process retained from cold work
until explicit quit. All 468 mappings are released. Those capacities are virtual
backing, not resident peaks or actual packing traffic. Outputs, explicit data
costs and backend events agree across the Lean variants and matched C scopes.

## Verification and limits

The full runner and independent directory/ZIP replay passed. All 39 source
observation tests passed against the full raw record; mutation cases reject a
foreign runtime, omitted variant, wrong entry-thread profile, changed toolchain,
misordered report, wrong error-object sizes and forged allocation claims. Every
repository snapshot was compared to its actual Git blob. Executables and Lake
caches are omitted from the compact archive; their hashes/sizes remain recorded.
The nested calibration's binaries are retained as evidence and never executed by
the verifier. Hashes provide integrity/correspondence, not authenticity.

The publication verifier additionally checks actual linked support-library paths
against the calibration and replays both this record and the independent
[Linux record](../2026-11-01-linux-allocator/RESULTS.md). The observed run-phase
counts agree. These later verifier checks do not change the measured revision or
raw observations.

Publication validation passed all 41 tests with
`python3 -m unittest discover -s experiments/source_workspace -p 'test_*.py'`,
including both retained exports and the support-library mutation. The ten
`SourceAllocatorRecord` cases also passed with the Linux archive selected through
`VASTITAS_SOURCE_ALLOCATOR_RECORD`. Dependency-boundary, diff and local Markdown
link checks passed.

The observer objects occupy 43,732 static bytes, separately from the source-call,
selected-site and backend observers; code, strings, alignment, stack and reporting
costs are excluded from that figure. Reporting begins after the final snapshot.
No operation clocks run. Stock runtime counts are not inferred from diagnostic
counts. Requested counters remain incomplete/cumulative; raw peaks are not
per-operation peaks. Startup on the waiting initialization thread, other
allocators, backend packing/static metadata, residency and other source profiles
remain outside this channel. The largest fixture is not representative evidence
for memory-bound performance. Tiny/bulk budgets, controlled Linux measurement and
the historical Stage 1 completion gate remain open.
