# Runtime-shape output and cost audit

This experiment checks actual public protocol-8 source, its emitted operations,
and a matched direct-CBLAS implementation. It records **correctness and explicit
costs only**. It does not measure speed or close the Fast like C gate.

Build the current frontend and kernel first, then run:

```sh
cargo build --locked
lake -d lean-kernel build
python3 experiments/runtime_shapes/run.py \
  --prefix /path/to/pinned-openblas \
  --output /tmp/runtime-shape-audit
python3 experiments/runtime_shapes/verify.py /tmp/runtime-shape-audit
python3 -m unittest discover -s experiments/runtime_shapes -p 'test_*.py'
```

On macOS explicitly add `--no-leak-sanitizer`: Apple ASan has no LSan. Linux
runs leave it enabled. OpenBLAS must be the pinned sequential LP64 0.3.34 build;
the environment requests one thread and the actual backend is checked. The
normal compiler remains independent of this optional experiment and backend.

## What actually runs

Each of four real/complex × ordinary/transposed profiles first passes unmodified
public `check`, `build`, and execution. That source calls one resource routine
at two different extent/padding tuples and writes each caller-owned output twice.
The compiler expands resource calls at their source call sites: the public
emission has four GEMM instructions, all calling the existing generic native ABI.
There is no new general resource-function code-sharing implementation.

A distinct retained one-call source is independently checked and emitted. Its
experimental wrapper replaces only the initial four scalar constant bindings
with Nat arguments. It preserves the generated pure extent arithmetic, native
narrowing, all guards, allocation/fill/drop instructions, and both identical
GEMM instructions. The wrapper introduces callable/looping benchmark boundaries;
these boundaries are **not** attributed to public compiler output. All source,
wire, original emission, wrapper, generated C, and transformation segments are
retained. An unexpected code-generation envelope fails closed.

Each wrapper process invokes the same compiled parameterized body at six shapes:
tiny rectangular, differently padded rectangular, modest rectangular, and each
zero axis. Both full lifecycle and explicit setup-hoisted reuse run with 1, 3,
and 7 repetitions. Each repetition writes the same destination twice. The reuse
scope hoists allocation, input fill, extent arithmetic/narrowing, and layout
guards; it includes two real native GEMM calls and their physical preflight.
This is an explicit caller-level experiment, not an inferred compiler optimization.

## Independent comparison and checks

The C implementation uses the same explicit arena allocations and layouts,
checked extent arithmetic, shape/layout conditions, pinned backend, complete
physical operand preparation, scalar/shape/output-separation checks, and write
counter preflight. It calls CBLAS directly, without `vgemm_execute`, intermediate
packing, copies, or a slow alternative arithmetic algorithm. Its zero-inner
overwrite explicitly fills zero; zero-output cases never call BLAS. Input
transpose is explicit; complex inputs are not conjugated.

The source's inputs are uniform exact values: real A=1/B=2; complex A=1+i and
B=2−i. The independent full-buffer oracle expects 2k or 3k+ki at **every** output
cell and unchanged input cells. Private allocation instrumentation fills every
physical component with a fixed NaN payload before the actual logical fills;
every padding component must retain those exact bits. Poisoning and these
checks are observer work and are excluded from reported production write costs.
Corrupting an output/padding component must fail the oracle. Standalone C/native
tests also preserve all bytes/counters on invalid leading dimensions and
saturated write counters, and compare the actual adapter with direct CBLAS.

Three generated scalar failure cases per profile cover the LP64 extent bound,
Nat values beyond UInt64, and extent arithmetic beyond the signed native range.
They must fail without stdout, finalize their arena, and leave no live data.
These cases test the generated Lean boundary; C accepts UInt64 parameters and
does not claim equivalent arbitrary-precision Nat inputs. Its arithmetic checks
are separate from the nine observed Lean scalar narrowings.

## Cost meanings and limits

For width w, capacities `(lda * physical_columns_A, ldb * n, ldc * n)`, and R
repetitions, the full lifecycle creates R arenas; reuse creates one. Each creates
three handles, but data `malloc/free` counts include only nonzero capacities.
Each arena uses two metadata allocation events. Peak data equals w times the
sum of capacities. Logical initialization writes w(mk+kn) per lifecycle; each
repetition adds 2wmn output bytes. Copied bytes remain zero. Source-level lifecycle
preflight observes six guards and nine Nat narrowings; neither is repeated in
the setup-hoisted scope. Actual BLAS calls are 2R only when m, k and n are nonzero.
`verify.py` independently reconstructs all costs and physical-buffer hashes.

Arena counters cover arena data and metadata, not all Lean heap objects, IO
result boxes, allocator internals, BLAS workspace/packing, or OS memory. The
allocation audit is a separate experiment. Guard/narrowing hooks, poisoning,
coordinate scans and FFI observation intentionally perturb execution; no timing
is recorded. Any later timing comparison must remove those observer costs,
retain full/setup-hoisted scope distinctions, and preserve independent output
validation. A shared-host run cannot establish controlled-host performance
acceptance or full source/native refinement.
