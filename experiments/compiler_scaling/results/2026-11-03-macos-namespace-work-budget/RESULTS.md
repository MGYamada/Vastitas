# Namespace budgets for a complete public request

The same Rust CLI ran `check --manifest-path` against the integrated baseline
`76cad69bdac44a691f054b374a4e1430c63b26ec` and the namespace change
`8c63c0a99b3283947cd62dc492faada42148c0a4`. Each row is one matched
observation on an uncontrolled arm64 Mac running macOS 27.2. Kernel order
alternated across cases. The input and executable hashes, elapsed times,
process outcomes and diagnostics are in [observations.json](observations.json).

| Public input | Baseline (s) | Candidate (s) | Candidate outcome |
| --- | ---: | ---: | --- |
| One call through 1,000 aliases | 1.445 | 2.205 | Accepted |
| 300 calls through the same 600 aliases | 1.594 | 0.870 | Accepted |
| Two separate modules with 1,050 aliases each | 3.699 | 0.072 | `E_LIMIT` across import declarations |
| 24 unused functions with 100 calls each through 600 aliases | 9.558 | 3.575 | `E_LIMIT` across the input and body passes |
| 72 unused functions with 100 calls each through 600 aliases | Deadline at 20 s | 0.426 | `E_LIMIT` before legacy adaptation |
| 300 lets in a six-argument method applicable to 4,096 keys | 0.049 | 0.050 | Existing program-wide elaboration `E_LIMIT` |

The baseline accepted the two-module and 24-function inputs. The harness
terminated its 72-function process group at the deadline. Both kernels
rejected the expanded dispatch body. The 1,000-alias single-use case cost
0.760 s more on this run. Reusing the 600-alias target saved 0.724 s.
These observations measure compiler admission. Generated numerical performance
has a separate acceptance gate.

Build both kernels and the baseline Rust CLI, then run the comparison from
the repository root with an unused output path.

```sh
python3 experiments/compiler_scaling/results/2026-11-03-macos-namespace-work-budget/compare.py \
  <baseline-checkout> <candidate-checkout> <output.json>
```

The namespace regressions also build and run the shared-alias program,
reject a bad unused body and verify that a rejected build preserves its
previous output. The [scope and charging rules](../../../../docs/packages.md)
apply to legacy, indexed and resource requests.
