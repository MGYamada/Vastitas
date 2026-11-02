# Storage checker indexing observation

The indexed implementation reduces repeated lookup work, but **#422 is still
open**. A 512-deep reborrow chain still exceeds the 30-second observation deadline.
Whole-state audits, writer pairs and nested call replay remain superlinear.

This is one warmed observation per actual protocol-8 source case on an
uncontrolled macOS arm64 host. Runs were sequential, with the reference series
before the indexed series; they were not randomized or repeated statistical
trials. They measure `vastitas check`, not generated-program speed, and do not
establish Fast like C or controlled Linux acceptance.

## Reproduction and provenance

Reference: `195b59f16e38999d8d366a0ce66b4be76b82d6ad`.
Indexed implementation: `33d5854c6ad6b638aa7631e360bc87c1fb01a69f`.
The same Rust CLI from the reference checkout was used for both kernel roots.
[observations.json](observations.json) retains kernel and source hashes, exit
codes, timeouts and warmup observations. All 15 comparison source hashes match.
The separate source generator is [check_storage_scaling.py](../../../../scripts/check_storage_scaling.py).

After building both kernels and the reference CLI:

```sh
python3 scripts/check_storage_scaling.py --compiler <reference>/target/debug/vastitas \
  --kernel-root <reference>/lean-kernel --sizes 64 128 256 --timeout 30 --output reference.json
python3 scripts/check_storage_scaling.py --compiler <reference>/target/debug/vastitas \
  --kernel-root <indexed>/lean-kernel --sizes 64 128 256 --timeout 30 --output indexed.json
python3 scripts/check_storage_scaling.py --compiler <reference>/target/debug/vastitas \
  --kernel-root <indexed>/lean-kernel --sizes 512 1000 --shapes allocate_drop read_loans --output larger.json
python3 scripts/check_storage_scaling.py --compiler <reference>/target/debug/vastitas \
  --kernel-root <indexed>/lean-kernel --sizes 512 --shapes reborrow_chain --timeout 30 --output remaining.json
```

Each invocation checks a trivial resource program before measuring the cases.
On timeout the harness terminates the compiler process group; the observed
`E_INTERRUPTED` is not a semantic rejection or a compiler work-budget diagnostic.
The reference and remaining-limit invocations intentionally exit nonzero.

## Selected observations

| Public source shape | Size | Reference seconds | Indexed seconds |
| --- | ---: | ---: | ---: |
| Allocate/drop pairs | 256 | 0.251 | 0.097 |
| Simultaneous shared reads | 256 | 1.639 | 0.306 |
| Disjoint write children | 128 | 7.762 | 0.445 |
| Disjoint write children | 256 | timeout at 30 | 3.134 |
| Nested reborrow chain | 128 | timeout at 30 | 1.270 |
| Nested reborrow chain | 256 | timeout at 30 | 9.979 |
| Shared reads behind ten wrappers | 256 | timeout at 30 | 6.248 |

The indexed checker also accepts 1,000 allocate/drop pairs in 0.834 seconds and
1,000 simultaneous shared reads in 4.199 seconds, within the existing source work
budget. Its 512-deep reborrow chain times out at 30.017 seconds. No full-complexity
or elapsed-time bound is inferred from these observations.

## Independent correctness validation

The implementation proves equality to the original audit for every state and
uses those equations as Lean `csimp` replacements. It retains all transition,
join, call-replay and code-generation audits. New forged-state regressions cover
duplicates, cycles, missing parents, sibling aliases, initialization and access
permissions. Existing safety theorems continue to use the same audit predicate.

Local validation passed: `cargo fmt --check`; strict locked Clippy;
`cargo test --locked --all-targets` (376 passed, 13 optional numerical tests ignored,
35 suites); kernel build (185 jobs); complete kernel regression script (152 jobs);
oracle build (186 jobs); 25,466-declaration axiom audit; and
`bash scripts/check_storage_native.sh` (sanitizers, exact emitted schedules,
failure cleanup, allocation counters and four fresh-process FFI scenarios).
The full Rust run was repeated with the required process permissions after two
existing child-process tests were denied by the sandbox. The successful rerun
had no failed tests. Documentation equality/limits and Python compilation passed.
The optional numerical adapter was not changed or locally retested here.
