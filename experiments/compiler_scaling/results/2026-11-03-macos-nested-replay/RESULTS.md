# Replaying identical resource call slices

Each public source package holds 200 shared read loans in a leaf function.
Forwarding functions call the leaf directly or through 10 or 30 wrappers.
Both kernels check the same source bytes with the same Rust CLI. The table
gives medians in seconds for two recorded checks after one warmup per
kernel/workload. Kernel order alternated across repetitions. All 36 checks
accepted on the local arm64 macOS 27.2 host. CPU affinity, frequency and
background load were uncontrolled. [Raw observations](observations.json)

| Wrappers | Static baseline | Static candidate | Runtime-shape baseline | Runtime-shape candidate |
| ---: | ---: | ---: | ---: | ---: |
| 0 | 0.249 | 0.207 | 0.194 | 0.168 |
| 10 | 2.159 | 0.749 | 1.603 | 0.583 |
| 30 | 11.218 | 1.844 | 8.561 | 1.463 |

The baseline already reuses the checked library's synthetic probes. The
candidate also reuses a completed child call's replay when both the entire
caller state and the entire action list match. Each enclosing call keeps its
own callee identity, exact statement slice and return/exit checks. Runtime
receipts include the ordered guard list. Differences in either input cause
the resource checker to replay the new pair. The final entry schedule is
independently checked. The remaining
depth cost includes actual expansion of each function probe and the entry.
These timings describe compiler checking.

| Input | Revision or SHA-256 |
| --- | --- |
| Baseline revision | `e49bebc3dc5f803080d3dc5518817c4462848a4f` |
| Baseline kernel | `aa9794e1f428514cb137b6bc56f951920b8d29a332b0bb54e73a759fa4489789` |
| Candidate revision | `a23a179a00c003c075f02c96792c602c92830b1a` |
| Candidate kernel | `e7106584457c4f66281d4ee9fe8ce097eb3f8ae9025dd92aa6122bc1b98edbe0` |
| Common Rust CLI | `4850cb677203efb04fea370496987c480b64a9b4cdbad8db6e49bcf24aa014a9` |

Build both kernels and run the command below for each checkout, with
`--profile static` and `runtime` and `--wrapper-depth 0`, `10` and `30`.
The JSON records the input hash, warmups, individual timed runs and exits.

```sh
python3 scripts/check_storage_scaling.py \
  --profile static --shapes wrapped_reads --sizes 200 --wrapper-depth 30 \
  --compiler /path/to/vastitas --kernel-root /path/to/lean-kernel --timeout 60
```
