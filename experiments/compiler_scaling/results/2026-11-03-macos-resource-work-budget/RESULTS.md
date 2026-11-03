# Admitting bounded resource-checking work

The same public Rust CLI checked each source against baseline
`76cad69bdac44a691f054b374a4e1430c63b26ec` and candidate
`41315c3af9a3fd3a9d0f23b366aa31af60ce820b`. The baseline already includes
the loan-chain audit, checked probe reuse and identical nested replay.
Each cell is one elapsed check on uncontrolled arm64 macOS 27.2. Kernel
order alternated across cases. All 24 processes finished within the 20-second
observation deadline. [Input and executable hashes, outcomes and times](observations.json)

| Public source | Baseline (s) | Candidate (s) | Candidate result |
| --- | ---: | ---: | --- |
| 200 static reads, 30 wrappers | 1.904 | 2.889 | Accepted |
| 200 runtime reads, 30 wrappers | 1.643 | 1.500 | Accepted |
| 512 static reborrows | 0.818 | 0.914 | Accepted |
| 512 runtime reborrows | 0.695 | 0.757 | Accepted |
| 512 static allocate/drop pairs | 0.199 | 0.187 | Accepted |
| 64 disjoint write children | 0.079 | 0.081 | Accepted |
| 256 disjoint write children | 2.025 | 0.349 | `E_LIMIT`, weighted work |
| 1,300 runtime reads | 0.708 | 0.113 | `E_RESOURCE_LIMIT`, existing expansion bound |
| 200 static reads, 90 wrappers | 5.249 | 3.192 | `E_LIMIT`, weighted work |
| 200 runtime reads, 90 wrappers | 4.216 | 2.055 | `E_LIMIT`, weighted work |
| One borrowed input forwarded 32 times | 0.230 | 0.266 | Accepted |
| One borrowed input forwarded 48 times | 0.823 | 0.963 | Accepted |

The previous checker accepted the three weighted-limit negatives. Both
kernels rejected the 1,300-loan input. The candidate identifies the required
primitive steps before expanding those loans. The 30-wrapper static case
shows the cost of metering on an admitted program. These measurements cover
compiler checking. Native execution time and controlled-host acceptance are
tracked separately.

The closed component regression also accepts a 4,096-action allocation/drop
plan and checks its final work receipt. Public regressions run the two
30-wrapper sources and reject 90 wrappers even when the main function never
calls the chain. A failed build preserves the existing output file.

Use `scripts/check_storage_scaling.py` to reproduce the allocation, loan,
write-child and reborrow sources. Use `--shapes wrapped_reads --sizes 200`
with `--wrapper-depth 30` or `90` and either profile. The borrowed-input
case uses one read parameter of type `Read<F64, 1, 1>` on each function.
The full source generator and matched invocation are in the comparison script.

```sh
python3 compare.py <baseline-checkout> <candidate-checkout> <new-json-output>
```
