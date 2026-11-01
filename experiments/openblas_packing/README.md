# Actual OpenBLAS GEMM packing observation

This optional experiment records the actual D/Z GEMM packing calls in pinned
sequential LP64 OpenBLAS 0.3.34. It extends the
[workspace observation](../openblas_workspace/README.md) with kernel names,
physical source rectangles, destination spans, and the exact enclosing CBLAS
route. The main compiler, native adapter and checked source semantics are unchanged.

Counting an operand once misses repacking in blocked multiplication. Each
observed copy contributes `m * n * components * 8` logical payload bytes, including
repeated copies of the same input. These bytes describe the calibrated packing
kernel's contiguous output and corresponding logical reads. They do **not**
measure bus traffic, cache misses, prefetching, elapsed time or whole-process cost.

The retained [macOS](results/2026-11-01-macos/RESULTS.md) and
[Linux](results/2026-11-01-linux/RESULTS.md) records measure clean feature `db62d22`.
Each retains all 1,828 executions and the actual shape/stride footprint checks:
136 contracts / 544 direct executions on macOS, 133 / 532 on Linux.
They observe 308,750 / 385,254 packing calls and 4,508 / 4,484 bytes in the named
static metadata set. Backend configurations differ; these are not timing comparisons.
The reports link the initial schema-1 records with their original grid limitation;
their measured revisions and claims remain distinct from these schema-2 records.

## Reproduce

```sh
python3 experiments/openblas_packing/run.py \
  --out /tmp/packing-record-new --build-dir /tmp/packing-build-new \
  --archive /path/to/OpenBLAS-0.3.34.tar.gz --jobs 4
python3 experiments/openblas_packing/verify.py /tmp/packing-record-new
VASTITAS_PACKING_RECORD=/tmp/packing-record-new \
  python3 -m unittest discover -s experiments/openblas_packing -p 'test_*.py'
python3 experiments/openblas_packing/archive.py \
  /tmp/packing-record-new /tmp/packing-export/evidence.zip
```

Record and build directories must be new, separate and outside the checkout.
Linux CI selects `--target HASWELL`; macOS uses host detection. The runner clears
inherited compiler/Make/preload options, pins the release archive, and uses the
ordinary sequential build options. It does not disable small-matrix or GEMV
shortcuts or force warmup behavior. Each command, source, configuration, input,
object hash, raw observation and executable is retained. Toolchains and system
libraries are recorded, not made hermetic. Verification accepts directories or
ZIPs without extracting or executing archived code; hashes detect inconsistency,
not authenticity.

## Observation and calibration

The private patch accepts exactly four SHA-256-pinned upstream files. It activates
copy hooks only in D/Z GEMM drivers, route hooks only in D/Z CBLAS interfaces, and
the existing backing/loan hooks in `memory.c`. Every other object must retain its
stock hash. In particular the actual compute, copy, GEMV and small-matrix kernel
objects remain unchanged; other level-three operations do not inherit the hooks.
Threaded, dynamic-architecture, fused, alternate precision and unsupported backing
allocator profiles are rejected. These are instrumented drivers, not unchanged
stock allocation or timing measurements.

Direct calls to every selected packing symbol check exact coordinate permutation,
unchanged input/padding and guarded output borders for 23 positive dimensions
from 1 through 257, all pairs of dimensions, and two leading-dimension paddings.
Both backends run plain and ASan/UBSan harnesses. Schema 2 additionally reconstructs
every distinct `(kernel,m,n,lda)` from the actual diagnostic records, then checks
that exact shape/stride on both plain/sanitized stock/diagnostic kernels. This
covers actual blocks outside the initial grid, such as extent 512 and large
leading dimensions. Missing or duplicate footprint receipts are rejected.
Upstream kernel objects themselves
are not sanitizer-instrumented. This is a finite calibration, not a theorem about
arbitrary dimensions or out-of-contract zero-size direct kernel calls. Zero-size
GEMM is tested through CBLAS and the actual adapter instead.

There are 457 fixture cases, each executed in two fresh processes per variant:
1,828 executions / 914 stock-diagnostic pairs. They include the existing workspace
calibration and 24 actual-adapter cases (overwrite, accumulate and failure before
writes), plus 432 direct CBLAS cases. The latter cross real/complex, both operands'
N/T/C modes, overwrite/accumulate, padded column-major layouts and twelve shapes:
empty outputs, zero inner dimension, vector-shaped and tiny products, a 256-square
product, `(2,50000,7)`, `(3,5,2051)`, `(2051,5,7)` and `(17,19,23)`.
Fixtures use alpha one and beta zero/one; other coefficient choices are outside
this calibration. Coordinate-varying integral values and an independent periodic integer oracle
check every output and unchanged input/padding word; T and C remain distinct.

Each actual route is classified as empty, GEMV, small-matrix or packed GEMM.
Packing events must use a calibrated symbol with the correct role/transpose,
fit the actual input rectangle and an active observed pool loan, avoid caller
storage and occur within that CBLAS call. The verifier independently reconstructs
the union of copied input rectangles, so padding and omitted required regions
cannot masquerade as complete coverage. Workspace events cannot occur within a
copy kernel or cross operation phases. Pool return is not deallocation.

GEMV and small-matrix routes preserve their actual algorithm and are explicitly
reported with **unavailable** packing payload, not zero total storage or traffic.
Their internal stack/local copying still requires separate attribution. No
observer changes a route decision or substitutes a slower packing algorithm.

## Static metadata and limits

The report supplies `sizeof` for the actual pool/release arrays, overflow pointers,
release counter, allocation lock, base address, initialization/overflow flags,
huge-page flag and constructor flag in `memory.c`. Linux warmup fields are present
only when compiled. Array units and LP64 fields are independently checked. The
sum is the declared storage for this named set, not complete backend/static-image
size; it excludes linker alignment, other translation units, read-only dispatch
tables, stack, TLS and libc internals. Dynamically allocated overflow tables are
already in the separate backing-request channel, not these static sizes.

Observer storage is separately reported for its fixed 16,384 copy records and
256 route records. Callbacks allocate nothing and read no clocks. Capacity,
thread, nesting and lifecycle failures terminate the observation even with
`NDEBUG`. Reporting occurs after the last operation and explicit backend quit.
Observer bytes exclude alignment, code, strings, stack and reporting allocations.
Do not add logical packing, borrowed capacity, backing requests, arena bytes and
observer bytes into one purported heap/traffic total: their meanings overlap.

Joining this calibration to actual generated-source call spans is a subsequent
required cost measurement. The [Stage 1 gate](../../docs/stage1-completion.md)
also retains startup/other-allocator/general-peak attribution, representative
cache-resident and memory-bound workloads, material tiny-call overhead and its
predeclared absolute budget, and controlled-host equivalent-C acceptance. A
dedicated Linux host is currently unavailable; these observations do not waive
the gate or establish native refinement or floating-point field laws.
