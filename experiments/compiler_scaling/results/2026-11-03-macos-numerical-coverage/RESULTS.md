# Checking positions of numerical receipts

The actual public kernel checked the same captured protocol-8 JSON with and
without the positional receipt audit. All 56 invocations accepted. The table
shows median wall time over three timed runs after one warmup per binary and
case. The order of the two binaries alternated each round. Each invocation
started a new kernel process. The macOS arm64 host had uncontrolled affinity,
background load and frequency. These observations measure compiler checking.
Generated-program timing and the controlled-host performance gate are separate.

| Public check case | Before (ms) | With coverage (ms) |
| --- | ---: | ---: |
| storage-128 | 34.85 | 34.18 |
| gemm-128 | 51.38 | 51.34 |
| branches-calls-64 | 37.14 | 36.73 |
| contraction-tree | 54.38 | 54.25 |
| storage-512 | 221.22 | 221.91 |
| gemm-768 | 237.31 | 236.39 |
| branches-calls-512 | 115.23 | 116.09 |

The baseline is `3e92718104dfab06c9b9fe68a42657149e38c012` (kernel SHA-256
`51d2851730a96767d72964cbbd8322b502331022b4180fcb1ee65534a3bdb5a2`).
The candidate is `3d8de05ac108b2879132ee4e0bd604120006a7c3` (kernel SHA-256
`43bfab37f4ad4646def7167e23a301323403e1bbac6b3632de8e56885efe7302`).
The [observations](observations.csv) include request bytes, hashes, warmups
and individual samples. Absolute temporary manifest paths contribute to the
request hashes.

To reproduce the case shapes, create a resource main with 128 or 512 successive
one-element F64 allocations and drops for the storage cases. For the GEMM
cases, use the real module and profiles from
[`examples/packages/numerical`](../../../../examples/packages/numerical).
Replace its first overwrite GEMM with 128 or 768 copies and call the real
product once from main. Keep the later accumulate and cleanup. For the two
branch cases, emit the overwrite inside both arms of a literal-true branch
with 16 or 128 copies per arm, and call the product twice. The contraction
tree case uses the unmodified
[tree package](../../../../examples/packages/contraction-tree). Capture each
Rust request once via `VASTITAS_KERNEL`, then send those bytes to each
`vastitas-kernel check` and verify `ok` for every run.
