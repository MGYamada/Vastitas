# Two-edge contraction-tree measurements

Times are ns/operation; IQR is Q25–Q75. Ratio is median of paired generated/C ratios.
Lifecycle is the emitted public resource program; reused_buffers includes four FFI calls and physical preflight. The four primitive diagnostic scopes exclude FFI and time one selected pack/regroup/BLAS call, while executing the complete two-stage schedule.

| Case | Scope | Generated median [IQR] | C median [IQR] | Paired ratio [bootstrap 95%] |
|---|---|---:|---:|---:|
| tiny-complex-p0 | lifecycle | 1144.3 [1131.0, 1146.0] | 771.8 [769.9, 780.6] | 1.455 [1.449, 1.487] |
| tiny-complex-p0 | reused_buffers | 481.0 [478.5, 484.3] | 368.1 [365.0, 374.0] | 1.293 [1.283, 1.329] |
| tiny-complex-p0 | pack3_adapter | 39.3 [38.2, 39.4] | 17.8 [17.7, 17.9] | 2.203 [2.116, 2.207] |
| tiny-complex-p0 | regroup3_adapter | 32.0 [32.0, 32.6] | 18.9 [18.9, 19.0] | 1.704 [1.683, 1.746] |
| tiny-complex-p0 | first_blas | 82.7 [82.5, 83.2] | 79.6 [79.5, 80.5] | 1.034 [1.030, 1.043] |
| tiny-complex-p0 | second_blas | 127.1 [124.8, 127.2] | 123.2 [123.1, 123.9] | 1.032 [0.982, 1.035] |
| tiny-f64-p1 | lifecycle | 1061.8 [1048.2, 1061.9] | 741.2 [729.9, 741.5] | 1.432 [1.396, 1.478] |
| tiny-f64-p1 | reused_buffers | 431.2 [420.4, 439.4] | 311.7 [308.8, 317.5] | 1.384 [1.267, 1.463] |
| tiny-f64-p1 | pack3_adapter | 36.8 [36.6, 38.0] | 16.9 [16.6, 17.1] | 2.248 [2.160, 2.267] |
| tiny-f64-p1 | regroup3_adapter | 32.1 [32.1, 32.5] | 19.0 [18.9, 19.0] | 1.691 [1.687, 1.738] |
| tiny-f64-p1 | first_blas | 63.0 [62.0, 63.1] | 62.0 [61.7, 62.2] | 1.013 [0.983, 1.024] |
| tiny-f64-p1 | second_blas | 75.4 [75.4, 75.5] | 77.0 [76.8, 77.7] | 0.978 [0.962, 0.988] |
| tiny-complex-p1 | lifecycle | 1182.4 [1179.7, 1182.8] | 805.4 [793.7, 819.1] | 1.469 [1.420, 1.505] |
| tiny-complex-p1 | reused_buffers | 501.9 [497.7, 502.0] | 374.2 [372.2, 377.8] | 1.333 [1.316, 1.342] |
| tiny-complex-p1 | pack3_adapter | 37.2 [36.6, 37.3] | 17.9 [17.8, 18.0] | 2.084 [1.974, 2.104] |
| tiny-complex-p1 | regroup3_adapter | 33.4 [33.2, 33.9] | 18.8 [18.7, 18.9] | 1.775 [1.745, 1.860] |
| tiny-complex-p1 | first_blas | 98.1 [90.0, 131.8] | 90.9 [86.6, 138.5] | 0.902 [0.889, 1.190] |
| tiny-complex-p1 | second_blas | 127.8 [127.6, 128.2] | 126.7 [125.1, 205.7] | 1.015 [0.447, 1.036] |
| tiny-f64-p0 | lifecycle | 972.8 [971.8, 986.3] | 640.3 [638.2, 643.0] | 1.519 [1.503, 1.572] |
| tiny-f64-p0 | reused_buffers | 429.7 [422.9, 433.0] | 315.7 [313.5, 318.8] | 1.335 [1.318, 1.402] |
| tiny-f64-p0 | pack3_adapter | 37.0 [36.7, 37.0] | 17.0 [16.6, 17.1] | 2.151 [2.145, 2.274] |
| tiny-f64-p0 | regroup3_adapter | 32.4 [32.1, 33.1] | 19.0 [18.9, 19.1] | 1.703 [1.696, 1.774] |
| tiny-f64-p0 | first_blas | 61.9 [61.2, 63.7] | 62.4 [62.1, 63.1] | 0.992 [0.976, 1.024] |
| tiny-f64-p0 | second_blas | 73.9 [73.7, 78.1] | 75.3 [74.3, 75.9] | 1.003 [0.967, 1.093] |
