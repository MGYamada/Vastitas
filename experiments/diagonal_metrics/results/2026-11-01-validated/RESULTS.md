# Prepared diagonal operation measurements

C adapter versus equivalent C in prepared-pointer and matched-preflight scopes; excludes public source, Lean FFI, lifecycle, metadata construction, and backend allocations.
The first two pairs warm up each case; nine alternating-order pairs remain. Times are medians in ns/operation; ratio is the median of paired ratios. This shared host run is exploratory, with no performance acceptance claim.

| Scope | Operation | Scalar | Shape n × m | Adapter ns | C ns | Paired ratio [min, max] |
|---|---|---|---:|---:|---:|---:|
| prepared | adjoint | real | 1 × 1 | 16.2 | 2.2 | 7.257 [7.235, 7.432] |
| prepared | adjoint | real | 3 × 5 | 25.1 | 6.2 | 4.047 [4.013, 4.057] |
| prepared | adjoint | real | 64 × 96 | 2107.7 | 1747.7 | 1.218 [1.190, 1.307] |
| prepared | adjoint | real | 192 × 256 | 15468.8 | 15734.4 | 0.985 [0.972, 0.993] |
| prepared | pair | real | 1 × 1 | 102.5 | 15.4 | 6.687 [6.582, 6.800] |
| prepared | pair | real | 3 × 1 | 105.4 | 16.1 | 6.550 [6.330, 6.635] |
| prepared | pair | real | 256 × 1 | 391.4 | 94.5 | 4.148 [4.116, 4.210] |
| prepared | pair | real | 4096 × 1 | 4903.7 | 1555.3 | 3.165 [3.098, 3.178] |
| prepared | adjoint | complex | 1 × 1 | 17.5 | 2.2 | 7.593 [7.514, 8.353] |
| prepared | adjoint | complex | 3 × 5 | 52.3 | 18.5 | 3.211 [1.942, 4.442] |
| prepared | adjoint | complex | 64 × 96 | 3544.6 | 3344.6 | 1.055 [0.977, 1.135] |
| prepared | adjoint | complex | 192 × 256 | 25234.4 | 25609.4 | 0.985 [0.938, 1.093] |
| prepared | pair | complex | 1 × 1 | 115.9 | 25.5 | 4.524 [4.437, 5.814] |
| prepared | pair | complex | 3 × 1 | 116.0 | 27.3 | 4.288 [4.206, 4.380] |
| prepared | pair | complex | 256 × 1 | 949.9 | 679.1 | 1.398 [1.388, 1.402] |
| prepared | pair | complex | 4096 × 1 | 14438.5 | 12032.8 | 1.200 [1.179, 1.228] |
| checked | adjoint | real | 1 × 1 | 16.2 | 16.6 | 0.976 [0.974, 0.992] |
| checked | adjoint | real | 3 × 5 | 25.1 | 23.8 | 1.053 [1.049, 1.061] |
| checked | adjoint | real | 64 × 96 | 2116.9 | 1916.9 | 1.110 [0.980, 1.150] |
| checked | adjoint | real | 192 × 256 | 15578.1 | 15750.0 | 0.987 [0.974, 0.994] |
| checked | pair | real | 1 × 1 | 105.7 | 104.4 | 1.014 [0.995, 1.133] |
| checked | pair | real | 3 × 1 | 104.4 | 102.6 | 1.012 [1.000, 1.023] |
| checked | pair | real | 256 × 1 | 391.7 | 363.4 | 1.079 [1.064, 1.089] |
| checked | pair | real | 4096 × 1 | 4952.9 | 5211.1 | 0.950 [0.940, 0.963] |
| checked | adjoint | complex | 1 × 1 | 17.2 | 16.8 | 1.024 [0.586, 1.055] |
| checked | adjoint | complex | 3 × 5 | 30.5 | 29.1 | 1.060 [0.970, 1.182] |
| checked | adjoint | complex | 64 × 96 | 3584.6 | 3510.8 | 1.016 [0.926, 1.073] |
| checked | adjoint | complex | 192 × 256 | 24812.5 | 26062.5 | 0.952 [0.941, 1.080] |
| checked | pair | complex | 1 × 1 | 113.7 | 111.8 | 1.020 [1.003, 1.032] |
| checked | pair | complex | 3 × 1 | 115.8 | 116.6 | 0.996 [0.990, 1.006] |
| checked | pair | complex | 256 × 1 | 953.5 | 953.1 | 0.999 [0.977, 1.004] |
| checked | pair | complex | 4096 × 1 | 14366.8 | 14504.1 | 0.991 [0.976, 0.993] |

All 352 output/cost pairs match, including both weighted scratch and scalar output. The four sanitizer cases also pass. Repeated operations allocate/copy zero arena data bytes and write exactly mn scalar-width bytes per adjoint or (n+1) scalar-width bytes per pairing. Both sides reuse padded caller storage; C receives pre-realized double coefficients, while the adapter decodes and validates immutable binary64 bits. Both sides record the same write-counter calls. The checked C scope repeats the complete applicable physical/bit/backend/counter preflight with the same primitive validators before writes; the prepared scope deliberately excludes those checks. Pairing uses the identical pinned sequential OpenBLAS GEMM; internal backend allocation is not counted.

Setup (excluded): arena allocation/fill, coefficient allocation/encoding, pointer preparation. The harness creates four coefficient tables totaling 32·max(n,m) bytes; this is harness metadata, not generated-program allocation evidence. Production generated constants hold 8·(n+m) bytes for explicit adjoint diagonals or 8·n bytes for pairing (identity/scaled identity uses 8 bytes per metric), plus Lean object/container overhead. Public generated execution, Lean metadata initialization/lifetime, full lifecycle, total/backend allocation and controlled-host acceptance remain separate obligations. See the checked-source/native regressions and the Stage 1 gate.
