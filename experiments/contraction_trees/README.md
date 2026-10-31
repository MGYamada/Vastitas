# Public two-edge contraction tree versus matched C

This experiment compiles a real protocol-8 package with `contract_tree`, executes
its canonical executable, and benchmarks the independently emitted public program
against explicit C. It uses the same sequential LP64 OpenBLAS 0.3.34 archive for
both implementations. A passing smoke run establishes execution, coordinate,
padding, cleanup and cost contracts; it is not C-performance acceptance.

The finite computation is `T[i,k,j] A[k,a] B[j,b] -> C[i,a,b]`. Both implementations
perform exactly this written order:

1. Optimized `pack3`: `[i | k,j] -> [i,j | k]` into caller scratch.
2. Overwrite GEMM with A, producing middle `[i,j | a]`.
3. Generic `regroup3`: `[i,j | a] -> [i,a | j]` into the same scratch allocation.
4. Overwrite GEMM with B, producing `[i,a | b]`.

There are six caller allocations: T, A, B, scratch, middle, C. Source releases and
reborrows explicitly separate scratch uses. The C baseline performs the first
contiguous x-block copy, a coordinate loop for the second regroup, and direct
CBLAS calls with matching layouts, coefficients, arithmetic order and physical
preflight. It calls neither the production packing nor GEMM adapter for these
operations. Both sides use the same arena allocation/setup primitives, so this
comparison does not isolate allocator choice. Generic network planning, rank-2
regrouping and larger trees are outside this benchmark.

## Reproduce

Build the frontend and kernel, then provide the repository-pinned OpenBLAS prefix:

```sh
cargo build --release --locked
lake -d lean-kernel build
python3 -m unittest discover -s experiments/contraction_trees -p 'test_*.py'
python3 experiments/contraction_trees/run.py \
  --prefix /path/to/pinned-openblas --output /tmp/tree-smoke \
  --smoke --samples 3 --target-ms 0.1
```

On macOS add `--no-leak-sanitizer` explicitly because Apple ASan lacks LSan. Linux
uses ASan/UBSan/LSan by default. `--frontend` and `--kernel` accept already-built
binaries; no build or acceptance fallback is allowed. `--cc` selects the C compiler
for both the canonical build and private instrumented build. Output directories
must not exist.

The default full mode omits `--smoke`, uses 11 paired samples and targets 5 ms per
batch. It includes tiny `(2,3,4,5,6)`, small `(7,17,5,11,13)` and bulk
`(24,40,32,48,56)` dimensions, crossed with real/complex and padded/contiguous
storage: 12 cases. The small case needs a larger first scratch footprint than the
second; the others need a larger second footprint. Source size remains bounded:
three fills and six sparse patches initialize the inputs, plus six full-allocation
sentinel fills. Three coordinate assertions also execute in the canonical program.

The [Linux workflow](../../.github/workflows/contraction-tree-experiment.yml) runs
four-case smoke validation on both push and pull-request events affecting the
harness or its compiler/runtime dependencies. Manual dispatch also offers the full
twelve-case profile with eleven pairs per scope and a 5 ms calibration target:

```sh
gh workflow run contraction-tree-experiment.yml --ref REVIEWED_REF -f profile=full
```

Both profiles require actual public check/build/execution, native ASan/UBSan/LSan
validation and identical output/cost pairs, with one BLAS thread and a 45-minute
job cap. Compact source/command/validation/measurement records and large
disassembly/symbol files are retained as separate artifacts for fourteen days.
Preserve selected evidence and its exact measured revision before artifact expiry.
Shared-runner timings remain exploratory; they do not satisfy controlled-host
performance acceptance, and a calibration target does not guarantee the duration
of later samples.

## What is timed

| Scope | Timed work |
| --- | --- |
| `lifecycle` | Complete emitted arena lifecycle, six allocation/init/drop operations, four numerical operations and three output assertions; metadata and cleanup included |
| `reused_buffers` | Repeated actual emitted pack3/GEMM/regroup3/GEMM instructions, including all four FFI calls and adapter preflight |
| `pack3_adapter` | First packing adapter or matched C packing; FFI excluded |
| `regroup3_adapter` | Second regrouping adapter or matched C regroup; FFI excluded |
| `first_blas` | Actual first CBLAS call only |
| `second_blas` | Actual second CBLAS call only |

The lifecycle wrapper removes only terminal printing. For reused and diagnostic
scopes it explicitly hoists the emitted allocation/setup and cleanup around a
runtime repetition loop; this experimental transformation is not a claim that the
public source supports a dynamic loop. Every diagnostic scope still executes the
complete four-operation schedule in order. Only its selected interval contributes
to elapsed time. Primitive clock overhead is included; it matters for tiny inputs.
Standalone C-adapter selftest timings are validation rows, not public timings.

Each process executes one untimed generated lifecycle before selecting the measured
implementation. The runner separately executes canonical check/build/run, sends the
captured protocol-8 input to the actual kernel check/emit path, and keeps exact
emitted instructions in the wrapper. Unexpected codegen envelopes fail closed.
Private instrumented runtime copies leave production files unchanged.

## Oracles and costs

A coordinate oracle uses only input constants/patches, never BLAS or packed data.
It checks every input, middle and output coordinate, every padding/sentinel cell,
and the full scratch allocation. The scratch oracle applies the second footprint
over the first: first-pack values outside the second footprint remain observable.
The oracle uses long-double sparse corrections for the first contraction and an
explicit second-axis sum. Fixtures use small dyadic values; generated and C output
hashes must match exactly in addition to the independent tolerance checks.

Native validation corrupts each buffer and padded prefix, checks invalid shape,
grouping and alias failures preserve output/counters, and independently replaces
each packing with a wrong logical flat copy. Each mutation must change both the
buffer oracle and final product, with padding left intact. Optimized and sanitized
native checks must pass before any generated timing is accepted.

Let `w` be 8 or 16 bytes, `P = w*i*k*j`, `R = w*i*j*a`, `M = R`, and
`C = w*i*a*b`. Each four-operation sequence writes `P+R+M+C` bytes and copies
exactly `P+R` bytes.
There is no implicit reset between iterations. Per-lifecycle setup writes all six
allocated capacities once, plus `w*(i*k*j+k*a+j*b+6)` for input fills/patches.
The three output assertions write no bytes. A lifecycle has six allocations/frees;
reuse scopes allocate/free none during the timed interval. Peak data bytes are the
sum of all six capacities, including max-sized scratch and padding. Every paired
row must agree on output, allocations, frees, copies, writes and cleanup counters.
Both implementations finish with zero arena live bytes.

The runner alternates pair order, warms each scope, calibrates a common repetition
count and retains every sample. Calibration targets batch duration, not a guarantee
that later batches exceed the target. It preserves paired median ratios/deltas,
bootstrap intervals, and the ratio of separate medians; these statistics can differ
under host variation. No noisy hosted or laptop result establishes the controlled
host performance gate.

## Recorded evidence and limitations

`cases.json`, generated packages, captured wire, kernel response, exact generated
source, wrapper, private instrumented runtime, commands and compile times are kept.
Full run output also records toolchain/backend hashes, compiler flags, explicit
thread settings, native/sanitizer rows, raw paired CSV, summaries, symbols/disassembly
and linked libraries. Compact result bundles may retain hashes of large inspection
files instead of their contents; each result record states what it includes.
Command logs remain bounded. Linux selects an allowed CPU unless `--cpu` is provided;
macOS records that affinity is unavailable. The final input-hash audit rejects a
run if recorded compiler binaries, runtime or source inputs changed while it ran.

Arena counters exclude Lean heap, allocator internals and BLAS-private memory.
`process_maxrss_kib` can include a launcher's pre-exec footprint on Linux and is not
an isolated executable heap measurement. Sanitizers and output checks support this
finite runtime path, not native refinement or ideal floating-point field laws.
The BLAS scopes are attribution diagnostics; library use alone is not a performance
result. Release evidence in `results/` states exactly which commands actually ran.
