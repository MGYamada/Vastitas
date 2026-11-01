# Runtime-shape correctness and explicit costs, macOS

The final run passed on 2026-11-01, 00:42:55–00:43:25 UTC (30.35 seconds of
orchestration). **No operation timings were measured.** This is output,
preflight, cleanup and explicit-cost evidence. It does not establish performance
parity, a controlled-host acceptance result, or full source/native refinement.

The measured checkout had base commit
`117a6e972308f25b8ddccd9db536af161d6a322a` and uncommitted runtime-shape changes.
The complete dirty-path listing is in [environment.json](environment.json).
Do not attribute this run to a later feature/integration commit or a subsequent
production IO-result optimization. The archive retains 45 selected source/input
snapshots; the environment also hashes the exact frontend, kernel executable,
OpenBLAS archive and two backend headers. All 50 recorded hashes were unchanged
at the end of the run. These are selected snapshots plus exact binary identities,
not a claim that every compiler source file was archived.

```sh
python3 experiments/runtime_shapes/run.py \
  --prefix /tmp/vastitas-openblas-verified \
  --output /private/tmp/vastitas-runtime-shape-audit-final \
  --no-leak-sanitizer
python3 experiments/runtime_shapes/verify.py \
  experiments/runtime_shapes/results/2026-11-01-macos/evidence.zip
python3 -m unittest discover -s experiments/runtime_shapes -p 'test_*.py' -v
```

The toolchain and native logs record macOS arm64, Apple Clang, pinned Lean 4.35.0,
and sequential LP64 OpenBLAS 0.3.34 with one thread. Apple ASan has no LSan;
`--no-leak-sanitizer` was explicitly supplied. Linux and whole-process leak
instrumentation were not run here. Arena live-byte and allocation/free checks
are separate from LeakSanitizer and general Lean-heap accounting.

## Actual executions

- Four unmodified public package `check`/`build`/executions passed: real and
  complex, each with ordinary or explicitly transposed rectangular A.
  Each public executable uses two different runtime extent/padding tuples,
  writes each caller destination twice, and returns `0`.
- Their actual public emissions each contain four GEMM instructions. Resource
  functions still expand per source call site; this evidence adds no general
  resource-function code-sharing model.
- Four independently checked one-call emissions supplied experimental wrappers.
  Only the initial m/k/n/pad scalar bindings were parameterized. The wrappers
  preserve pure extent arithmetic, all narrowing/guards, explicit allocation,
  fills/drops and both identical native GEMM instructions. Callable/looping
  wrapper boundaries are instrumentation, not public compiler output.
- Each wrapper process ran six shapes through that same compiled body:
  `(m,k,n,pad) = (2,3,4,0), (3,5,2,2), (17,13,19,3), (0,3,4,1), (2,0,4,1),
  (2,3,0,1)`. Lifecycle and setup-hoisted reuse scopes used 1, 3 and 7 repeats.
- There are 48 wrapper execution commands, 288 recorded rows and 144 matched
  generated–C pairs. The independent Python verifier recomputed every row's
  dimensional costs and complete physical-buffer hash.
- Eight standalone native records (four optimized, four ASan/UBSan) cover all
  six shapes, direct-C versus actual adapter outputs, every source/output cell
  and padding component, deliberate corruption detection, invalid leading
  dimensions, and saturated write-counter failure preservation. Each record
  contains 12 scope/shape rows; all were independently re-audited.
- Twelve generated narrowing/bound failures (three per profile) emitted no
  stdout and reported finalized arenas, zero data allocations/frees and zero
  live data. They cover an extent above INT32_MAX, a Nat above UInt64, and
  arithmetic above the signed native size bound. They are actual generated
  failures, not a claim that the C UInt64 input boundary accepts arbitrary Nat.
- Four harness regression tests passed with the measured run. After independent
  review, the verifier was tightened to require the exact scenario matrix and
  complete native/failure coverage; two mutation tests were added. All six
  current harness tests pass. This verifier-only hardening changes no measured
  source emission, runtime input or raw record; the archive retains the original
  measured helper snapshots honestly.

The public executable's terminal `0` is an execution check. The independent
numerical and full-padding oracle runs in the separately identified wrappers
and native tests; it is not silently inserted into the public source executable.

## Matching work and observed costs

The C path uses the same scalar representation, layouts, explicit transpose,
overwrite policy and backend. It performs checked extent arithmetic and physical
operand/scalar/shape/output-separation/accounting preflight before direct CBLAS.
It does not call the GEMM adapter, copy/pack inputs, or use a slower multiplication
algorithm. Zero-inner overwrite writes zero; any zero axis causes zero actual
CBLAS calls. The complex path uses A=1+i and B=2−i without conjugation.

All output cells equal the independent exact reference: real `2k`, complex
`3k+ki`. All input cells and every padding component are unchanged. Padding was
poisoned with a fixed NaN payload by private observer code; poison writes and
oracle scans are test work excluded from the production-write counter. Their
overhead is one reason this record contains no timings.

For R repetitions, each of which overwrites the same destination twice:

| Cost | Full lifecycle | Explicit setup-hoisted reuse |
| --- | --- | --- |
| Arenas | R | 1 |
| Data allocation/free events | R × nonzero capacities | nonzero capacities |
| Metadata allocation events | 2R | 2 total, 0 in scope |
| Peak arena metadata here | 280 bytes | 280 bytes |
| Logical writes, width w | Rw(mk + kn + 2mn) | w(mk + kn) + 2Rwmn total; 2Rwmn in scope |
| Copied bytes | 0 | 0 |
| Observed source/layout guards | 6R | 0 in scope |
| Observed Lean Nat narrowings | 9R | 0 in scope |
| Actual BLAS calls, all axes nonzero | 2R | 2R |

The reuse scope explicitly hoists setup arithmetic/narrowing/guards and retains
both native GEMM operations and their physical preflight. C receives UInt64
parameters and checks its arithmetic; it has zero Lean Nat narrowings. This
reported difference is the only excluded field in pair equality. The guard
counter counts emitted shape/layout guard sites, not every native conditional.

Peak data is width times the sum of all three padded capacities. For example,
the real normal tiny case uses 208 bytes, the real normal padded case 392 bytes,
and its transposed counterpart 360 bytes. All data allocation/free counts match,
and all arenas finish with zero live data. Metadata sizes are native ABI facts
for this run, not portable constants.

Arena counters exclude Lean IO boxes/general heap, allocator internals, BLAS
private packing/workspace and OS memory. No interpreter is introduced: the
retained generated code contains direct compiled arithmetic/guards and native
calls. Checker proofs and whole-toolchain/native refinement remain separate.
The Fast like C gate stays open.

## Retained record

[evidence.zip](evidence.zip) contains 247 members and 833,583 bytes. SHA-256:
`81ca0b631fa9f70d14e2bb4371ce58fec87aebb96178ca1d0424e076b0341c8a`.
[manifest.json](manifest.json) records every member's size/hash and the five
plain JSON copies. It includes the original source/wire, public and wrapper
responses, emitted Lean, parameterized wrappers, actual generated C, private
native inputs, command logs, symbols, 45 source snapshots and all raw records.
The large executable/object/static-library files are not retained.

The independent [verifier](../../verify.py) passed on both the original run
directory and this archive: 288 records, 144 pairs, 45 source snapshots,
8 native records and 12 failure-cleanup records. No preliminary smoke run is
substituted for this final stable-input record.
