# Stage 1b indexing: issue #141 follow-up

## Starting point

On 2026-10-28, issue [#141](https://github.com/MGYamada/Vastitas/issues/141)
was closed by merged [PR #167](https://github.com/MGYamada/Vastitas/pull/167).
This follow-up starts from main `5d12a7e2cb4d3a41d7bbf0ef69c684abe588b994`.
A final main check found `10454414dc1684df82e1dad6a8861bf1e19343f8`;
its only subsequent changes were the stdlib ADR and its design-index link.
The compiler sources are identical to the measured `5d12a7e` baseline.
That baseline already contains the State definition/instance/global indexes,
active-set membership and constant-time stack pop, the two separate lowering
passes, an indexed final static audit, and a lambda-containing 20,000-function
watchdog case. Those changes are retained, not reimplemented.

The remaining semantic gap was audit completeness: the main audit index retained
only the last definition of each identity. For a forged ledger with two `f`
definitions of types `Fn<Int, Int>` and `Fn<Bool, Int>`, a call to the former
satisfied `StaticCallsValid` but failed `staticCallsValid`. This is a false
rejection of the audit helper's existential specification; it is not evidence
that a duplicate source program bypasses declaration validation.

## Correspondence and order

- `definitionLookup` is the ordinary lookup index. Its theorem proves exact
  agreement with `List.find?`, including first-declaration behavior on duplicates.
  The original ordered definitions remain the driver of each lowering pass.
- `definitionIndex` is rebuilt inside the backend from `lowered.definitions`.
  It stores all definitions of each identity, in list order. A proof field states
  that each bucket equals the original list filter; the proof is runtime-erased.
- `staticCallsValid_iff` proves equivalence with `StaticCallsValid` on every
  ledger, including duplicate identities and signatures. Targets and function
  bindings use full structural type equality. Probe arguments are rejected.
  No uniqueness assumption or frontend-provided index is needed for the theorem.
- The existing `checkSurfaceProgram_static_calls` now applies this equivalence
  to the actual `lowerFunctions` result, and retains acceptance of that same
  lowered core by `checkModule`.

The ordered declaration list, call ledger and generated function array are not
reordered by hash iteration. The scheduler still uses its explicit active stack
for cycle diagnostics, set membership for recursion detection, and stack pop/set
erasure on completion. Signature probes never enter executable state. Body fuel,
the administrative worklist bound and the 4096-specialization limit are unchanged.

For normally prepared distinct identities, buckets have one element. Expected
index construction and target auditing cost is linear in definitions plus
recorded targets/bindings, excluding hashing and structural signature comparison
costs. Forged duplicate-heavy ledgers scan the matching bucket, not all unrelated
definitions. This is not a worst-case hash-table bound or a claim that the entire
compiler is linear.

## Regression and reproduction

`VastitasKernel.FunctionRegression` covers first/middle/last duplicate signature
witnesses, missing identities/signatures, same-arity type mismatches, invalid
function-argument contracts, probes and distinct identities with equal rendered
names. It compares the executable index against the independent original
predicate. Public acceptance cases pin dependency output order with shared
callees and with/without an unrelated lambda, and preserve duplicate diagnostic
precedence. Rust tests exercise shared higher-order memoization through native
output (42), both declaration orders, and unchanged cycle diagnostics.

`kernel_checks_twenty_thousand_functions_within_the_watchdog` retains the
60-second harness and checks four workloads: a plain forward chain, that chain
with an invoked lambda, the lambda chain in reverse declaration order, and
20,000 functions sharing a callee with an invoked lambda.

Build baseline and candidate kernels with the same pinned Lean version, then:

```sh
python3 scripts/benchmark_lowering.py \
  --baseline-kernel /path/to/baseline/vastitas-kernel \
  --kernel lean-kernel/.lake/build/bin/vastitas-kernel \
  --sizes 2000 4000 8000 --runs 3 > comparison.csv
```

The default matrix includes chain/shared call graphs, forward/reverse declaration
order, and lambda absent/present. The size counts the parameterized functions;
`main` and, when enabled, its lambda are additional. Every binary/workload receives
one warmup; measured runs alternate binary order. CSV includes individual samples,
median, minimum and maximum. Timings cover process startup, JSON decoding, both
lowering passes and final static/core audits. Payload construction and Rust
parsing are excluded. Rejected or timed-out workloads abort rather than produce
misleading timings. The script does not infer a speedup or assert a timing ratio.

## Validation record

Executed locally on Linux x86_64 (AMD EPYC 9V74, shared container), with pinned
Lean 4.35.0 release and Rust 1.99.1. The container exposes the current executable
at `/proc/self/exe` but restricts numeric `/proc/<pid>/exe`; Lean compilation
used a local compatibility shim for that self-path lookup. The measured kernel
subprocesses ran without the shim. Build/test jobs were finished before timing.
Dependency lockfiles and compiler limits were unchanged.

| Check | Result |
| --- | --- |
| `lake -d lean-kernel build` | Passed, including the new kernel equivalence proofs |
| `bash scripts/check_kernel_regressions.sh` | All eight targets passed, including expanded FunctionRegression |
| `lake -d lean build` | Passed, including Functions and all downstream oracle users |
| `(cd lean && lake env lean ../scripts/audit_axioms.lean)` | Passed for 6,386 declarations; standard allowed axioms only |
| `cargo fmt --check` | Passed |
| `cargo clippy --locked --all-targets -- -D warnings` | Passed |
| `cargo test --locked --all-targets` | 205 passed; all four 20,000-function watchdog workloads passed |
| `python3 scripts/check_boundaries.py` | Passed |
| `python3 -m unittest discover -s scripts -p 'test_*.py'` | 14 passed |
| CLI `check` / `build` of `examples/functions.vast`, then native execution | Passed; output 42 |
| Same duplicate-ledger fixture against main and candidate | Main: predicate true / index false; candidate: true / true |

The new Rust test initially used reserved `apply` and an unformatted diagnostic
expectation. Those fixture mistakes were corrected; the final full run above
passed. There are no `sorry`/`admit` additions. Local proof compilation had only
pre-existing mathlib module-system notices in unchanged oracle files.

Not executed here: hosted macOS/Linux CI for this branch, local macOS validation,
or the original issue's debug-CLI timing procedure. Native integration tests and
kernel regressions ran locally; this does not establish native-toolchain formal
correctness or an end-to-end compiler complexity bound.

## Measured comparisons

All numbers below are seconds, medians of three accepted runs after one warmup.
The workloads use `fi(x) = f(i+1)(x)` and a final identity. Unlike the issue's CLI
example, they do not add 1 at each edge and exclude Rust parsing. They therefore
must not be compared directly with the issue's 0.76 / 3.36 / 14.6 seconds.

Original issue commit `d620b2f8e9349d8d54b5ce036d0a2c26fad0f1d4` versus this
follow-up, using forward call chains (command adds `--orders forward --shapes chain`):


| Functions | Baseline plain | Baseline lambda | Candidate plain | Candidate lambda |
| --- | ---: | ---: | ---: | ---: |
| 2,000 | 0.146 | 0.517 | 0.143 | 0.152 |
| 4,000 | 0.400 | 1.852 | 0.360 | 0.320 |
| 8,000 | 1.297 | 8.181 | 0.998 | 1.176 |

[Raw samples: original comparison](benchmarks/stage1b-original-comparison.csv).

Already-fixed main `5d12a7e` versus this follow-up, forward-chain subset of the
full 24-workload matrix (chain/shared × forward/reverse × plain/lambda × 3 sizes):

| Functions | Baseline plain | Baseline lambda | Candidate plain | Candidate lambda |
| --- | ---: | ---: | ---: | ---: |
| 2,000 | 0.166 | 0.181 | 0.138 | 0.157 |
| 4,000 | 0.320 | 0.327 | 0.293 | 0.307 |
| 8,000 | 1.070 | 1.132 | 1.099 | 1.255 |

[Raw samples: full main comparison](benchmarks/stage1b-main-comparison.csv).
The candidate was measured separately in the two comparisons; run-to-run ranges
are in the CSV files. The major improvement over the issue commit already came
from #167. This follow-up repairs audit completeness and pins order/scale
regressions; it does not show a uniform additional speedup over the indexed main
(some cases are slower). The 8,000-function forward-chain timings also do not
justify a claim that total compilation is linear. No performance ratio is used
as a correctness assertion; the only scale regression deadline is the existing
per-process 60-second watchdog.
