# Prepared diagonal operation measurements

prepared C adapter versus prepared equivalent C; excludes public source, Lean FFI, lifecycle, metadata construction, and backend allocations.
The first two pairs warm up each case; nine alternating-order pairs remain. Times are medians in ns/operation; ratio is the median of paired ratios. This shared host run is exploratory, with no performance acceptance claim.

| Operation | Scalar | Shape n × m | Adapter ns | C ns | Paired ratio [min, max] |
|---|---|---:|---:|---:|---:|
| adjoint | real | 1 × 1 | 17.0 | 2.0 | 8.416 [8.359, 12.419] |
| adjoint | real | 3 × 5 | 27.0 | 6.0 | 4.487 [4.465, 4.532] |
| adjoint | real | 64 × 96 | 2640.0 | 1929.2 | 1.397 [1.361, 1.436] |
| adjoint | real | 192 × 256 | 19156.2 | 16062.5 | 1.192 [1.180, 1.199] |
| pair | real | 1 × 1 | 107.9 | 15.5 | 7.021 [5.055, 7.358] |
| pair | real | 3 × 1 | 110.3 | 15.7 | 7.074 [5.099, 7.306] |
| pair | real | 256 × 1 | 505.5 | 96.3 | 5.258 [5.106, 5.610] |
| pair | real | 4096 × 1 | 6293.0 | 1711.1 | 3.689 [3.660, 3.727] |
| adjoint | complex | 1 × 1 | 18.0 | 2.0 | 8.515 [7.410, 8.924] |
| adjoint | complex | 3 × 5 | 36.2 | 10.6 | 3.455 [3.244, 3.537] |
| adjoint | complex | 64 × 96 | 6055.4 | 3683.1 | 1.617 [1.507, 2.121] |
| adjoint | complex | 192 × 256 | 46515.6 | 28515.6 | 1.644 [1.202, 1.733] |
| pair | complex | 1 × 1 | 121.2 | 26.7 | 4.745 [4.289, 7.817] |
| pair | complex | 3 × 1 | 118.2 | 26.4 | 4.472 [4.358, 4.585] |
| pair | complex | 256 × 1 | 1046.2 | 679.7 | 1.542 [1.537, 1.561] |
| pair | complex | 4096 × 1 | 15807.4 | 11709.0 | 1.354 [1.343, 1.363] |

All 176 output/cost pairs match, including both weighted scratch and scalar output. The four sanitizer cases also pass. Repeated operations allocate/copy zero arena data bytes and write exactly mn scalar-width bytes per adjoint or (n+1) scalar-width bytes per pairing. Both sides reuse padded caller storage; C receives pre-realized double coefficients, while the adapter decodes and validates immutable binary64 bits. Both sides record writes. Pairing uses the identical pinned sequential OpenBLAS GEMM; internal backend allocation is not counted.

Setup (excluded): arena allocation/fill, coefficient allocation/encoding, pointer preparation. The harness creates four coefficient tables totaling 32·max(n,m) bytes; this is harness metadata, not generated-program allocation evidence. Production generated constants hold 8·(n+m) bytes for explicit adjoint diagonals or 8·n bytes for pairing (identity/scaled identity uses 8 bytes per metric), plus Lean object/container overhead. Public generated execution, Lean metadata initialization/lifetime, full lifecycle, total/backend allocation and controlled-host acceptance remain separate obligations. See the checked-source/native regressions and the Stage 1 gate.
