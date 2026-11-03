# Checking public reborrow chains

The public checker accepted a 512-deep write reborrow chain in both storage
profiles. The previous checker reached the 30-second deadline for both. Each
cell is a single wall-clock observation after an accepted warmup. The macOS
arm64 host had uncontrolled background load, CPU affinity and frequency. These
are compiler checks. Generated numerical runtime performance and the controlled
host acceptance gate have separate measurements.

| Shape and size | Static before | Static after | Runtime before | Runtime after |
| --- | ---: | ---: | ---: | ---: |
| Reborrow chain, 128 | 1.290 s | 0.110 s | 0.844 s | 0.115 s |
| Reborrow chain, 256 | 10.195 s | 0.322 s | 7.212 s | 0.332 s |
| Reborrow chain, 512 | 30 s deadline | 1.220 s | 30 s deadline | 1.110 s |
| Reborrow chain, 1000 | unsampled | 4.815 s | unsampled | 3.828 s |
| Shared readers, 128 | 0.094 s | 0.095 s | 0.082 s | 0.082 s |
| Writers¹, 128 | 0.439 s | 0.445 s | 0.304 s | 0.293 s |
| Ten wrappers over shared readers, 128 | 1.627 s | 1.629 s | 1.240 s | 1.231 s |

¹ The static case uses disjoint children of one owner loan. The runtime case
uses whole-map writers on distinct allocations. Compare before and after
within each profile.

The [observations](observations.json) retain all sample and warmup outcomes,
timeout exit codes, input source hashes, binary hashes and platform metadata.
The 12 paired inputs have matching source hashes. Two additional 1,000-deep
inputs ran on the candidate. Successful CLI output contains temporary manifest
paths and is represented by its checked exit status. The deterministic sources
come from the existing [source harness](../../../../scripts/check_storage_scaling.py).

Reference commit `d3d2c9ac2254c0f247df040a7e3dba9ab481e915`, candidate implementation `6f08929c4da10e41fbcc6cf7c0439f5130afda5d`.
Both variants used the same Rust CLI. The chain comparisons ran reference
before candidate. The control comparisons ran candidate before reference.
The harness timed one kernel invocation at a time. Sampling
order and the single-run design limit conclusions about small differences.

Reproduce the chain with each kernel and each `--profile static` or
`--profile runtime` using `--sizes 128 256 512 --shapes reborrow_chain
--timeout 30`. The static controls use `--sizes 128 --shapes read_loans
write_children wrapped_reads`. For the runtime controls, replace
`write_children` with `write_roots`. Supply the same `--compiler` and the
corresponding `--kernel-root` to every invocation.

The chain predicate validates exact first-match parentage and distinct loan
names. Other frames retain their reconstructed ancestry sets and writer checks.
Repeated frame audits, nested replay and program-wide resource work accounting
remain tracked in [#422](https://github.com/MGYamada/Vastitas/issues/422) and
[#423](https://github.com/MGYamada/Vastitas/issues/423).
