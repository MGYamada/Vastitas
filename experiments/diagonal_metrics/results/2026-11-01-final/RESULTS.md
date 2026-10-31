# Prepared diagonal operation measurements

C adapter versus equivalent C in prepared-pointer and matched-preflight scopes; excludes public source, Lean FFI, lifecycle, metadata construction, and backend allocations.
The first two pairs warm up each case; nine alternating-order pairs remain. Times are medians in ns/operation; ratio is the median of paired ratios. This shared host run is exploratory, with no performance acceptance claim.

| Scope | Operation | Scalar | Shape n × m | Adapter ns | C ns | Paired ratio [min, max] |
|---|---|---|---:|---:|---:|---:|
| prepared | adjoint | real | 1 × 1 | 16.5 | 2.3 | 7.218 [6.773, 8.105] |
| prepared | adjoint | real | 3 × 5 | 26.7 | 9.1 | 2.925 [2.898, 2.993] |
| prepared | adjoint | real | 64 × 96 | 2252.3 | 1984.6 | 1.124 [1.102, 1.267] |
| prepared | adjoint | real | 192 × 256 | 15921.9 | 16656.2 | 0.957 [0.926, 0.971] |
| prepared | pair | real | 1 × 1 | 107.6 | 15.5 | 6.895 [6.631, 6.978] |
| prepared | pair | real | 3 × 1 | 107.0 | 16.1 | 6.609 [6.298, 6.790] |
| prepared | pair | real | 256 × 1 | 392.5 | 94.0 | 4.177 [4.119, 4.209] |
| prepared | pair | real | 4096 × 1 | 4946.7 | 1377.0 | 3.594 [2.938, 3.640] |
| prepared | adjoint | complex | 1 × 1 | 16.9 | 2.2 | 7.565 [7.510, 7.633] |
| prepared | adjoint | complex | 3 × 5 | 28.2 | 9.7 | 2.915 [2.888, 2.928] |
| prepared | adjoint | complex | 64 × 96 | 3538.5 | 3418.5 | 1.029 [0.963, 1.079] |
| prepared | adjoint | complex | 192 × 256 | 27343.8 | 25703.1 | 1.068 [1.055, 1.089] |
| prepared | pair | complex | 1 × 1 | 114.9 | 26.1 | 4.399 [4.342, 4.485] |
| prepared | pair | complex | 3 × 1 | 117.7 | 27.3 | 4.302 [4.247, 4.340] |
| prepared | pair | complex | 256 × 1 | 957.4 | 681.0 | 1.409 [1.397, 1.429] |
| prepared | pair | complex | 4096 × 1 | 14409.8 | 11491.8 | 1.252 [1.242, 1.264] |
| checked | adjoint | real | 1 × 1 | 16.3 | 16.2 | 1.004 [0.975, 1.020] |
| checked | adjoint | real | 3 × 5 | 26.4 | 26.8 | 0.991 [0.979, 1.762] |
| checked | adjoint | real | 64 × 96 | 2301.5 | 2200.0 | 1.057 [0.667, 1.379] |
| checked | adjoint | real | 192 × 256 | 15859.4 | 17171.9 | 0.932 [0.882, 0.977] |
| checked | pair | real | 1 × 1 | 104.6 | 102.7 | 1.019 [1.008, 1.054] |
| checked | pair | real | 3 × 1 | 105.4 | 103.8 | 1.016 [1.010, 1.046] |
| checked | pair | real | 256 × 1 | 394.4 | 362.9 | 1.085 [1.082, 1.090] |
| checked | pair | real | 4096 × 1 | 5012.3 | 6280.7 | 0.800 [0.791, 0.808] |
| checked | adjoint | complex | 1 × 1 | 16.9 | 15.9 | 1.063 [1.043, 1.071] |
| checked | adjoint | complex | 3 × 5 | 28.2 | 27.2 | 1.038 [1.032, 1.044] |
| checked | adjoint | complex | 64 × 96 | 3510.8 | 3575.4 | 0.984 [0.939, 1.041] |
| checked | adjoint | complex | 192 × 256 | 27218.8 | 26000.0 | 1.048 [1.037, 1.061] |
| checked | pair | complex | 1 × 1 | 115.0 | 113.7 | 1.009 [1.003, 1.025] |
| checked | pair | complex | 3 × 1 | 116.8 | 116.5 | 1.006 [0.988, 1.022] |
| checked | pair | complex | 256 × 1 | 960.4 | 956.0 | 1.004 [0.985, 1.012] |
| checked | pair | complex | 4096 × 1 | 14375.0 | 14446.7 | 0.989 [0.961, 1.005] |

All 352 output/cost pairs match, including both weighted scratch and scalar output. The four sanitizer cases also pass. Repeated operations allocate/copy zero arena data bytes and write exactly mn scalar-width bytes per adjoint or (n+1) scalar-width bytes per pairing. Both sides reuse padded caller storage; C receives pre-realized double coefficients, while the adapter decodes and validates immutable binary64 bits. Both sides record the same write-counter calls. The checked C scope repeats the complete applicable physical/bit/backend/counter preflight with the same primitive validators before writes; the prepared scope deliberately excludes those checks. Pairing uses the identical pinned sequential OpenBLAS GEMM; internal backend allocation is not counted.

Setup (excluded): arena allocation/fill, coefficient allocation/encoding, pointer preparation. The harness creates four coefficient tables totaling 32·max(n,m) bytes; this is harness metadata, not generated-program allocation evidence. Production generated constants hold 8·(n+m) bytes for explicit adjoint diagonals or 8·n bytes for pairing (identity/scaled identity uses 8 bytes per metric), plus Lean object/container overhead. Public generated execution, Lean metadata initialization/lifetime, full lifecycle, total/backend allocation and controlled-host acceptance remain separate obligations. See the checked-source/native regressions and the Stage 1 gate.
