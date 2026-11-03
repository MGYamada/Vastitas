# Namespace lookup indexing observation

Reconstructed package/module/import/dependency indexes and persistent active
import sets reduce repeated work on long alias chains. **#426 remains open:**
completed resolutions are not memoized, there is no aggregate namespace work
budget, and Core typing contexts still have separate scaling costs.

These are compiler observations on an uncontrolled macOS arm64 host, not
runtime speed or Fast like C acceptance. Each case used one accepted warmup
per kernel followed by three measured runs, alternating baseline/candidate
order. This task launched no concurrent foreground build or test during the
measurement series; background load, CPU affinity and frequency were not
controlled. Three samples do not establish a confidence interval or a general
complexity bound. The smallest case shows no measurable improvement.

## Provenance and reproduction

Baseline kernel and the shared Rust CLI:
`7a83f55f04ced17da03d2e080356dc04543ef521`. Candidate implementation:
`91168fb664ecf58c5e93346856bbf97e740d7202`. The observation preceded the
documentation/evidence commit; the candidate binary hash is unchanged.

[observations.json](observations.json) retains both kernel hashes, the shared
CLI hash, exact source hashes, all warmup/sample times, exit codes and outputs.
The same manifest and source bytes were used for both kernels in each case.
All 32 warmup/sample invocations succeeded. Times include the actual CLI's
source parsing, kernel startup and full public checking.

After building both kernels and the baseline CLI, run the
[source harness](../../../../scripts/check_namespace_scaling.py):

```sh
python3 scripts/check_namespace_scaling.py \
  --compiler <baseline>/target/debug/vastitas \
  --baseline-kernel-root <baseline>/lean-kernel \
  --kernel-root <candidate>/lean-kernel \
  --runs 3 --timeout 60 --output observations.json
```

The harness terminates the compiler process group on its observation deadline.
A rejection or timeout stops the series with a failing exit status and is never
reported as a successful timing sample. This deadline is separate from the
compiler's own semantic/work limits.

## Median observations

| Chained imports | Calls through the first alias | Baseline seconds | Candidate seconds |
| ---: | ---: | ---: | ---: |
| 250 | 1 | 0.107 | 0.107 |
| 500 | 1 | 0.660 | 0.344 |
| 1,000 | 1 | 4.988 | 1.335 |
| 600 | 300 | 3.336 | 1.540 |

## Independent correctness evidence

The namespace oracle proves first-match equivalence for the reconstructed
tables, including duplicate input and complete package identity. It connects
the rich indexed-source tables to the same builder, and proves that the
persistent import set has exactly the previous list's cycle membership.
These facts concern the actual lookup functions; they are not timing theorems
or source/native refinement claims.

`tests/namespace_scaling.rs` checks all four positive shapes, builds and runs
the repeated-call case with result `42`, and retains rejection of an unused
ill-typed body, a 1,000-link cycle and a 1,500-link resolution-limit violation.
Direct kernel regressions additionally preserve first-record precedence for
duplicate packages/modules/imports/dependencies and reject mismatched package
versions. Existing visibility, authority and forged-IR cases remain enabled.

Validation passed: `cargo fmt --check`;
`cargo clippy --locked --all-targets -- -D warnings`;
`cargo test --locked --all-targets` (401 passed, 13 optional numerical tests
ignored, 38 suites); `lake -d lean-kernel build` (187 jobs);
`bash scripts/check_kernel_regressions.sh` (154); `lake -d lean build` (195);
`lake -d lean env lean scripts/audit_axioms.lean` (30,405 declarations,
4,115 private, including the strict least-fuel audit);
`bash scripts/check_indexed_native.sh` (23 standalone native fixtures);
`python3 -m unittest discover -s scripts -p 'test_*.py'` (393 tests);
`python3 scripts/check_docs.py`; and `python3 scripts/check_boundaries.py`.
The full Rust suite used the required process permissions after the sandbox
blocked two existing child-process inspection tests.
