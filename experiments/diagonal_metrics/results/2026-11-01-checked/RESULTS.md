# Prepared diagonal operation measurements

C adapter versus equivalent C in prepared-pointer and matched-preflight scopes; excludes public source, Lean FFI, lifecycle, metadata construction, and backend allocations.
The first two pairs warm up each case; nine alternating-order pairs remain. Times are medians in ns/operation; ratio is the median of paired ratios. This shared host run is exploratory, with no performance acceptance claim.

| Scope | Operation | Scalar | Shape n × m | Adapter ns | C ns | Paired ratio [min, max] |
|---|---|---|---:|---:|---:|---:|
| prepared | adjoint | real | 1 × 1 | 16.5 | 2.2 | 7.408 [7.332, 7.560] |
| prepared | adjoint | real | 3 × 5 | 26.1 | 8.5 | 3.084 [3.050, 3.094] |
| prepared | adjoint | real | 64 × 96 | 2566.2 | 2021.5 | 1.288 [1.237, 1.361] |
| prepared | adjoint | real | 192 × 256 | 18406.2 | 16140.6 | 1.140 [1.110, 1.147] |
| prepared | pair | real | 1 × 1 | 104.1 | 14.9 | 6.966 [6.870, 7.035] |
| prepared | pair | real | 3 × 1 | 106.4 | 15.6 | 6.819 [6.595, 6.916] |
| prepared | pair | real | 256 × 1 | 403.5 | 95.4 | 4.230 [4.104, 4.418] |
| prepared | pair | real | 4096 × 1 | 5043.0 | 23817.6 | 0.212 [0.210, 0.214] |
| prepared | adjoint | complex | 1 × 1 | 16.6 | 2.2 | 7.429 [7.173, 7.491] |
| prepared | adjoint | complex | 3 × 5 | 32.4 | 9.7 | 3.352 [3.318, 3.393] |
| prepared | adjoint | complex | 64 × 96 | 5507.7 | 3403.1 | 1.613 [1.535, 1.683] |
| prepared | adjoint | complex | 192 × 256 | 40984.4 | 25828.1 | 1.587 [1.580, 1.590] |
| prepared | pair | complex | 1 × 1 | 115.4 | 25.9 | 4.465 [4.398, 4.495] |
| prepared | pair | complex | 3 × 1 | 117.1 | 27.3 | 4.293 [4.142, 4.386] |
| prepared | pair | complex | 256 × 1 | 956.0 | 674.7 | 1.419 [1.410, 1.426] |
| prepared | pair | complex | 4096 × 1 | 14354.5 | 11930.3 | 1.197 [1.165, 1.255] |
| checked | adjoint | real | 1 × 1 | 16.6 | 16.2 | 1.026 [1.010, 1.034] |
| checked | adjoint | real | 3 × 5 | 26.1 | 26.4 | 0.989 [0.984, 0.999] |
| checked | adjoint | real | 64 × 96 | 2563.1 | 2055.4 | 1.251 [1.076, 1.302] |
| checked | adjoint | real | 192 × 256 | 18390.6 | 16515.6 | 1.113 [1.083, 1.120] |
| checked | pair | real | 1 × 1 | 103.4 | 102.5 | 1.015 [0.996, 1.032] |
| checked | pair | real | 3 × 1 | 106.6 | 106.1 | 1.011 [0.991, 1.046] |
| checked | pair | real | 256 × 1 | 403.1 | 368.7 | 1.094 [1.062, 1.097] |
| checked | pair | real | 4096 × 1 | 5079.9 | 28176.2 | 0.179 [0.140, 1.037] |
| checked | adjoint | complex | 1 × 1 | 16.7 | 16.2 | 1.032 [1.027, 1.059] |
| checked | adjoint | complex | 3 × 5 | 32.4 | 27.1 | 1.194 [1.173, 1.198] |
| checked | adjoint | complex | 64 × 96 | 5513.8 | 3501.5 | 1.562 [1.519, 1.622] |
| checked | adjoint | complex | 192 × 256 | 41046.9 | 26078.1 | 1.576 [1.549, 1.584] |
| checked | pair | complex | 1 × 1 | 115.0 | 113.8 | 1.017 [0.997, 1.146] |
| checked | pair | complex | 3 × 1 | 116.1 | 115.1 | 1.006 [0.994, 1.022] |
| checked | pair | complex | 256 × 1 | 971.8 | 976.4 | 1.004 [0.961, 1.025] |
| checked | pair | complex | 4096 × 1 | 14299.2 | 14586.1 | 0.980 [0.965, 0.994] |

All 352 output/cost pairs match, including both weighted scratch and scalar output. The four sanitizer cases also pass. Repeated operations allocate/copy zero arena data bytes and write exactly mn scalar-width bytes per adjoint or (n+1) scalar-width bytes per pairing. Both sides reuse padded caller storage; C receives pre-realized double coefficients, while the adapter decodes and validates immutable binary64 bits. Both sides record the same write-counter calls. The checked C scope repeats the complete applicable physical/bit/backend/counter preflight with the same primitive validators before writes; the prepared scope deliberately excludes those checks. Pairing uses the identical pinned sequential OpenBLAS GEMM; internal backend allocation is not counted.

Setup (excluded): arena allocation/fill, coefficient allocation/encoding, pointer preparation. The harness creates four coefficient tables totaling 32·max(n,m) bytes; this is harness metadata, not generated-program allocation evidence. Production generated constants hold 8·(n+m) bytes for explicit adjoint diagonals or 8·n bytes for pairing (identity/scaled identity uses 8 bytes per metric), plus Lean object/container overhead. Public generated execution, Lean metadata initialization/lifetime, full lifecycle, total/backend allocation and controlled-host acceptance remain separate obligations. See the checked-source/native regressions and the Stage 1 gate.
