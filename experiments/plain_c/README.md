# Standalone C comparators

The public GEMM, tensor-packing and contraction-tree experiments now compare
three implementations of each finite fixture:

| Arm | Implementation | Purpose |
| --- | --- | --- |
| `generated` | Actual checked source emission, Lean loop/FFI and the production arena/adapter with observation hooks | Measure generated execution |
| `arena_c` | C packing/CBLAS with the same arena, preflight and accounting | Attribute codegen/FFI overhead relative to that runtime |
| `plain_c` | Separate C11 executable with aligned allocations, explicit packing and direct CBLAS | Equivalent-C performance comparator |

Historical two-arm records called the second arm `c` or "direct C". Those
ratios measure generated/arena-C, including the runtime in both arms. They do
not measure the runtime overhead against standalone C. Their archived bytes,
revisions and measurements remain unchanged; they cannot be relabeled as
plain-C measurements. This implements the comparator correction in #431, not
the controlled-host Fast-like-C acceptance gate.

## Fixed work and timing boundaries

`probe.c` links only the host C libraries and the same pinned sequential LP64
OpenBLAS 0.3.34 archive as the generated arm. Validation audits its linked
symbols and rejects Vastitas storage, numerical-adapter or Lean symbols.
The fixture and backend contract are checked once, before measurement. The
primary timed loop contains no arena, per-call layout/backend preflight,
write accounting or diagnostic cost counters.

Each physical buffer uses `posix_memalign` with 64-byte alignment, the same
capacity, sentinel initialization, logical input fills and sparse patches.
No extra zero-fill is required. The scalar representation, N/N layouts, alpha,
beta, arithmetic order, explicit caller scratch and output observations match
the source fixture. The pack and regroup loops use contiguous x-block copies.
The tree reuses the same scratch allocation, preserving first-pack bytes
outside the second footprint. No planner, hidden scratch allocation, implicit
conjugation or alternate mathematical algorithm is introduced.

The lifecycle clock includes allocation, initialization, operations, output
observation and release for each arm. Reused scopes hoist each arm's setup and
cleanup while retaining every repeated pack/GEMM/regroup operation. Projection
scopes execute the complete schedule but time only the selected pack or CBLAS
call; timer overhead remains included and these are diagnostic scopes, not the
full operation. All arms use the same monotonic clock selection. A complete
untimed lifecycle warms each executable's backend before sampling.

Every case uses an independent coordinate oracle shared as source between the
three executables. It derives expected values from fixture coordinates and
constants, not from BLAS or the packing implementation. It checks every buffer,
padding cell, real/imaginary component and the actual accumulated repetition
count. Checksums and constant-size observations must also agree across arms.
Full verification is outside measured batches; reused buffers are verified after
every batch, and separate lifecycle verification brackets each sampling series.
Partial-allocation failure tests require all earlier allocations to be freed.

## Timing records and separate cost replay

The timing C executable is compiled **without** `BENCH_COSTS`. It reports
`cost_instrumentation: false` and no allocation/write/copy fields. In `raw.csv`
those fields are blank, meaning **unobserved**, never zero. A separately compiled
`BENCH_COSTS` executable replays the same operations and reports explicit logical
data allocations/frees, live/peak capacity, writes and copies. These costs must
match the arena diagnostic rows. Its heap metadata counters are zero because
the pointer table is on the stack; this does not mean zero stack storage,
allocator overhead or BLAS-private memory. Diagnostic timings are never admitted
to the three-arm timing summary. Neither build accounts for every physical
memory transaction or total process heap.

`harness.py` runs three fresh processes per group, with equal repetition counts
and all six permutations of implementation order. Six warmup groups precede
adaptive calibration against the fastest arm. Default full runs use twelve
measurement groups; smoke workflows use six. Other sample counts can leave an
incomplete final order cycle. Keep every sample and inspect minimum batch
duration; calibration does not guarantee later batches meet its target.

Summary schema 2 contains all three distributions and paired ratio/delta summaries
for `generated/plain_c`, `generated/arena_c` and `arena_c/plain_c`. Only the first
is the equivalent-C comparator. The 5,000-resample interval estimates within-run
variation, not host uncertainty or acceptance. The schema verifier rejects
missing/duplicate arms, mismatched repetitions/outputs/costs, invented plain-C
cost observations, invalid numbers and a diagnostic binary relabeled as timing.

## Validation and reproduction

The existing experiment runners execute actual frontend `check`, canonical
`build`/execution, independent Lean checking/emission, and the emitted wrapper
before reporting any generated comparison. Their READMEs describe each finite
profile and its exclusions. Standalone native validation can also run separately:

```sh
python3 -m unittest discover -s scripts -p 'test_plain_c_measurements.py'
python3 scripts/check_plain_c_baselines.py \
  --prefix /path/to/pinned-openblas --output /tmp/plain-c-validation
```

This runs all 48 fixtures (24 GEMM, 12 packing, 12 trees), optimized and with
fatal ASan/UBSan, comparing arena/adapter and plain-C timing/diagnostic outputs.
Add `--no-leak-sanitizer` on macOS; Linux CI retains LSan and adds `--valgrind`
for one padded complex fixture in each profile. The prebuilt BLAS archive is
not sanitizer-instrumented. `--smoke` restricts the native fixture sizes only;
neither mode is a performance measurement or public-source acceptance by itself.

Records retain source/header/backend hashes, compiler configuration, binary
hashes, symbol audits, commands, correctness/cost rows and cleanup failures.
The ordinary compiler and nonnumerical CI remain independent of OpenBLAS.
A controlled host, predeclared tiny-call budget and complete cost/representative
workload evidence remain necessary for Stage 1 performance acceptance.
