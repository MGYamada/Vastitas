# Reusing the checked resource library in the public entry

Each input holds 200 shared read loans in the leaf function. Main calls it
through the indicated number of forwarding functions. All twelve public checks
accepted. Each cell is a single wall-clock observation after an accepted warmup
with the same Rust CLI. The two kernels saw identical source bytes within each
pair. The order of baseline and candidate alternated across pairs. The macOS
arm64 host had uncontrolled background load, CPU affinity and frequency.

| Wrappers between main and leaf | Static before | Static after | Runtime before | Runtime after |
| ---: | ---: | ---: | ---: | ---: |
| 0 | 0.372 s | 0.249 s | 0.283 s | 0.181 s |
| 10 | 3.913 s | 2.103 s | 3.006 s | 1.596 s |
| 30 | 22.155 s | 11.344 s | 16.746 s | 8.621 s |

The public checker now retains the completed all-body probe batch for its
entry proof. It still expands real arguments from the actual caller and replays
nested call slices. Times continue to grow with call depth. This comparison
measures compiler checking, independently of generated-program runtime.

Baseline `e23d8c9a2bf114d2a24b8fd535f88d5ecef67c4c`, kernel SHA-256
`43bfab37f4ad4646def7167e23a301323403e1bbac6b3632de8e56885efe7302`. Candidate
`1c3f76c934059a606004ef40bb13813097439c28`, kernel SHA-256
`aa9794e1f428514cb137b6bc56f951920b8d29a332b0bb54e73a759fa4489789`. Rust CLI SHA-256
`4850cb677203efb04fea370496987c480b64a9b4cdbad8db6e49bcf24aa014a9`.
The [observations](observations.csv) retain request source hashes, individual
times and exit codes.

Run the existing [source harness](../../../../scripts/check_storage_scaling.py)
with both kernel roots, each profile and each wrapper depth. For example

```sh
python3 scripts/check_storage_scaling.py --profile runtime --sizes 200 \
  --shapes wrapped_reads --wrapper-depth 30 --timeout 60 \
  --compiler /path/to/vastitas --kernel-root /path/to/lean-kernel
```

The default depth of ten generates the same source bytes as the earlier
[#422](https://github.com/MGYamada/Vastitas/issues/422) and
[#423](https://github.com/MGYamada/Vastitas/issues/423) observations.
