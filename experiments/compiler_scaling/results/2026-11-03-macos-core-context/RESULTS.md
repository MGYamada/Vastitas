# Lexical lookup and result checking in long `let` bodies

Each public input starts with `let root: Int = 1;` and binds another 128, 512 or
1,600 values. Each addition reads either the previous binding or `root`.
The same debug Rust CLI checks each package against both compiled Lean kernels.
The smaller Core-only driver constructs the corresponding term before starting
its clock and measures the actual `Decidable (HasType …)` on that term.

The baseline is `bec8b9a7ee6a6d51e654fc02b528c73110264302`. The final
checker is `65970fea637fd2a943cb8e2ebd7c0087d53bc5e0`. The host was arm64
macOS 27.2 with Lean 4.35.0. CPU affinity, frequency and background load were
uncontrolled. These are compiler observations, separate from generated-program
performance and the controlled-host acceptance gate.

| Read | Extra lets | Public baseline (s) | Public candidate (s) | Core baseline (ms) | Core candidate (ms) |
| --- | ---: | ---: | ---: | ---: | ---: |
| Previous | 128 | 0.0317 | 0.0321 | 0.035 | 0.026 |
| Previous | 512 | 0.0894 | 0.0895 | 0.299 | 0.079 |
| Previous | 1,600 | 0.3457 | 0.2645 | 2.612 | 0.227 |
| Previous | 4,096 | — | — | 25.068 | 0.553 |
| Oldest | 128 | 0.0315 | 0.0319 | 0.043 | 0.026 |
| Oldest | 512 | 0.0889 | 0.0772 | 0.428 | 0.080 |
| Oldest | 1,600 | 0.3206 | 0.2958 | 3.684 | 0.229 |
| Oldest | 4,096 | — | — | 39.416 | 0.570 |

The table gives medians after one warmup for each workload and kernel. The
entry order alternates between runs. All 48 public invocations and 96 Core
invocations accepted. Public times include CLI startup, parsing and all checker
passes. Core times exclude process startup and term construction. Three public
samples and five Core samples per kernel/workload were timed.
[Public samples](public.csv) · [Core samples](core.csv)

The first implementation (`237b31a681a2995ef5805d5c60d106b0a9cbc2b0`)
indexed bindings and scope references. Its 1,600-binding oldest-read public
median rose from 0.2870 s to 0.3237 s. Each enclosing `let` was still walking
to the same terminal result to check its validity. The final checker derives
that fact from the recursively checked body through `letTyped_iff`.
[Lookup-only samples](lookup-only.csv)

| Executable | SHA-256 |
| --- | --- |
| Common Rust CLI | `47ddf899bc46f99747516f265b28407b04ff7fc540e496943317732b1136adfe` |
| Baseline kernel | `02ffe1ae72912585eb91b906fd881a1da1f6e879bd08dae21d6daeb10da7b3ca` |
| Lookup-only kernel | `c439e87328ea7a95c2989065b531a945b4c6f955d7964a68b168f540a85891da` |
| Final kernel | `e4b7ea29a14c2cd9a32ee754da114ca820aa3189347848fb7f8cc8034040859c` |

Build the baseline Rust CLI with `cargo build --locked` and both kernels with
`lake -d lean-kernel build vastitas-kernel` in their respective checkouts. Run
the following from the directory containing this record, using a new output
directory. The driver links the Core fixture against each kernel’s own compiled
objects. Public program generation, run order and clocks are in the harness.

```sh
python3 compare.py <baseline-checkout> <candidate-checkout> <new-output-directory>
```
