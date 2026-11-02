# Symbolic resource frame indexing observation

The reconstructed indexes reduce repeated symbolic-frame lookup work, but
**#423 remains open**. A 512-deep reborrow chain still reaches the 30-second
observation deadline. Whole-frame audits, writer pairs and call replay remain
superlinear; this change adds no global work budget.

These are single warmed observations on an uncontrolled macOS arm64 host.
Reference cases ran sequentially before indexed cases, without randomization or
repeated statistical trials. No concurrent foreground build/test was launched
by this task during the recorded series; background load and CPU affinity were
not controlled. The measurements concern `vastitas check`, not native runtime
speed or Fast like C acceptance.

## Provenance and reproduction

Reference: `3bf1f175b40f3170ac4d96e0cfc97cdcc8f5c7b1`, already including the
static resource audit indexes. Runtime index implementation:
`0d4e667c284a8e7a6e7cbe8aaf59f1fcadcdaa5c`. The same reference Rust CLI was used
with each kernel root. These observations isolate that increment before its
later integration with the diagnostic changes; they are not timing claims
about every later integration commit.

[observations.json](observations.json) retains kernel/source hashes, warmups,
exit codes and deadline results. All 15 comparison source hashes match. The
[source harness](../../../../scripts/check_storage_scaling.py) also retains
byte-identical generation for the original static cases.

After building the corresponding kernels and the reference CLI:

```sh
python3 scripts/check_storage_scaling.py --profile runtime \
  --compiler <reference>/target/debug/vastitas --kernel-root <reference>/lean-kernel \
  --sizes 64 128 256 --timeout 30 --output reference.json
python3 scripts/check_storage_scaling.py --profile runtime \
  --compiler <reference>/target/debug/vastitas --kernel-root <indexed>/lean-kernel \
  --sizes 64 128 256 --timeout 30 --output indexed.json
python3 scripts/check_storage_scaling.py --profile runtime \
  --compiler <reference>/target/debug/vastitas --kernel-root <indexed>/lean-kernel \
  --sizes 1000 --shapes read_loans --output larger.json
python3 scripts/check_storage_scaling.py --profile runtime \
  --compiler <reference>/target/debug/vastitas --kernel-root <indexed>/lean-kernel \
  --sizes 512 --shapes reborrow_chain --timeout 30 --output remaining.json
```

The reference and remaining-limit commands intentionally return nonzero. Their
`E_INTERRUPTED` comes from the harness terminating the compiler process group;
it is not a semantic rejection or an internal compiler work-budget result.

## Selected observations

| Public source shape | Size | Reference seconds | Indexed seconds |
| --- | ---: | ---: | ---: |
| Allocate/drop pairs | 256 | 0.257 | 0.110 |
| Simultaneous shared reads | 256 | 1.595 | 0.245 |
| Distinct-allocation write loans | 256 | 7.857 | 1.312 |
| Nested reborrow chain | 128 | timeout at 30 | 0.954 |
| Nested reborrow chain | 256 | timeout at 30 | 6.922 |
| Shared reads behind ten wrappers | 256 | timeout at 30 | 5.070 |

The indexed checker accepts 1,000 simultaneous runtime read loans in 3.542
seconds. Its 512-deep reborrow chain times out at 30.022 seconds. No full-complexity
or elapsed-time bound is inferred.

## Independent correctness evidence

`Shapes.auditFrame_eq_indexed` and `Shapes.compatibleWith_eq_indexed` prove
unconditional equality to the actual reference predicates. The compiled checker
uses these equations; existing frame-to-concrete theorems still refer to the
same audit. Thirteen malformed-frame cases, both writer/read pair orders and
zero-extent conflicting writers remain rejected. Five small generated source
profiles and the existing 80 concrete-valuation regressions passed.

After integration with the resource diagnostic changes, validation passed:
`cargo fmt --check`; `cargo clippy --locked --all-targets -- -D warnings`;
`cargo test --locked --all-targets` (391 passed, 13 optional numerical tests
skipped, 36 suites); kernel build (185 jobs); complete kernel regressions (152);
oracle build (186); and the 25,787-declaration axiom audit. The ordinary suite
used the required process permissions for its child-process tests.

The separately enabled `runtime_shape_source` numerical test also passed with
`VASTITAS_TEST_OPENBLAS_PREFIX` set to the pinned sequential LP64 OpenBLAS 0.3.34
installation. It builds and executes actual real/complex runtime source,
padding/empty axes and preflight-failure cases. Native behavior remains separate
from the frame-to-concrete proof. Documentation limits/equality, Python
compilation and unchanged static-source generation checks passed.
