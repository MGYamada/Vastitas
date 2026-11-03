# Cost of checking emitted-call occurrence coverage

This comparison charges the additional compiler audit that counts actual Core
calls by caller specialization and target. It measures the public protocol-2
kernel check on identical JSON inputs, excluding Rust parsing and payload
construction. It does not measure generated-program runtime or Fast like C.

Baseline: `1a4c5611d29788554f57085bc42b2795fd1bb65d` (kernel SHA-256
`5ff485064e56a5505478e503450a0555bba69e76bf09954681429a17b4b88ddc`).
Candidate: `9b7b36118683592bc1f9b73a9f1bc56d7f270020` (kernel SHA-256
`51d2851730a96767d72964cbbd8322b502331022b4180fcb1ee65534a3bdb5a2`).

Each input has 4,000 functions plus `main`. The chain calls the next function;
the shared graph calls one leaf. The lambda variant also invokes a lifted Fn
in `main`. The script ran one accepted warmup per binary/case and three
alternating baseline/candidate samples. All 32 checks accepted. No concurrent
foreground build/test was launched; background load, affinity and frequency
were uncontrolled on this macOS arm64 host. The small sample does not establish
a confidence interval, complexity bound or performance acceptance threshold.

| Graph | Lambda | Baseline median seconds | Candidate median seconds |
| --- | --- | ---: | ---: |
| Chain | No | 0.3612 | 0.3735 |
| Chain | Yes | 0.3635 | 0.3690 |
| Shared leaf | No | 0.2498 | 0.2580 |
| Shared leaf | Yes | 0.2572 | 0.2593 |

[Raw samples](observations.csv) retain all timed observations. The existing
four 20,000-function watchdog cases passed separately in the full Rust suite.

```sh
python3 scripts/benchmark_lowering.py \
  --baseline-kernel <baseline>/lean-kernel/.lake/build/bin/vastitas-kernel \
  --kernel <candidate>/lean-kernel/.lake/build/bin/vastitas-kernel \
  --sizes 4000 --orders forward --shapes chain shared --runs 3 --timeout 60
```
