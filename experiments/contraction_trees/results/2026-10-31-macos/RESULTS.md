# Two-edge tree smoke: 2026-10-31 macOS

The actual public source, canonical native executables, emitted-code wrappers,
matched C, and four-profile native/sanitizer checks passed. This is a correctness
and cost smoke record, not performance acceptance or a controlled-host comparison.

The recorded tree working directory had HEAD
`57810c6ea64ce461c77eca762cee6138f3a629d3` and an in-progress dirty merge of main
`0a1062845dc58f030bc946cf52598db81a5bc9f2`. Compiler/kernel/runtime source snapshots
and executable hashes are retained. The final audit found all 45 recorded input
hashes unchanged between capture and completion. These results are not attributed
to a future integration commit. Earlier preliminary runs are superseded here;
one prompted the input-stability guard after a shared frontend rebuild was found.

The command was:

```sh
python3 experiments/contraction_trees/run.py \
  --prefix /private/tmp/vastitas-openblas-verified \
  --output /private/tmp/vastitas-tree-smoke-stable-20261031 \
  --frontend target/debug/vastitas --smoke --samples 3 --target-ms 0.1 \
  --no-leak-sanitizer
```

It ran from 14:47:41.767788 to 14:48:13.832188 UTC (32.06 seconds). The frontend
was a debug build; generated native code and matched C used `-O3 -fno-lto`, with
no fast-math flags. The host reports macOS 27.2 arm64, Apple clang 21.0.0 and
Lean 4.35.0. OpenBLAS reports 0.3.34, `VORTEXM4 SINGLE_THREADED`, parallel=0,
threads=1, with LP64 and a host-specific static archive. CPU affinity is unavailable
on this host; the CPU-brand `sysctl` query was denied by the sandbox and is retained
as an optional metadata failure. No CPU model is inferred from that failed query.
ASan and UBSan passed; Apple LeakSanitizer was explicitly disabled. Linux LSan
remains pending. This was a shared development host, not an isolated timing host.

## Validation and measurements

- Four cases: real/complex × contiguous/padded, all with `(i,k,j,a,b)=(2,3,4,5,6)`.
- Four canonical public check/build/run paths and four independent kernel emissions
  plus wrapper executions passed. Each canonical source checks three output cells;
  the instrumented wrapper checks every input/middle/output/scratch/padding cell.
- Eight standalone native validation records (four optimized and four ASan/UBSan),
  containing 96 C/adapter rows. Both independently wrong flat-copy mutations were
  rejected by the buffer oracle and final product in each profile.
- Six scopes × four cases = 24 summary groups. There are 482 raw rows / 241 complete
  pairs, including 144 measured rows / 72 measured pairs (three per group).
  The additional 96 generated/C verification executions are kept in `commands.json`.
- Every pair matched output hash, allocation/free/cleanup, copy/write and metadata
  costs. Independent recomputation of all raw cost equations passed, all four
  wrapper/emission/source comparisons matched, and all 40 recorded relative source
  hashes matched their archived snapshots. The other five hashes identify the
  compiler/kernel binaries and external OpenBLAS archive/headers.
- All measured batches reached at least 0.1 ms in this run. This short target and
  three pairs are not sufficient for a performance conclusion; all samples remain.
- Canonical frontend builds totaled 6.95 seconds; private wrapper compilation
  totaled 9.17 seconds. These wall times are separate from operation timing.

Eight harness unit tests pass, including bounded command logs, unexpected-codegen
rejection, exact wrapper preservation, pair mismatch rejection, input hash changes,
scratch sizing in both directions, bounded source size, and both flat-copy output
mutations across all 12 full-mode fixtures. An additional optimized standalone
batch validated those 12 fixtures, including the case whose first scratch footprint
is larger than its second. It contributes 12 validation records / 144 rows under
`additional-native/`; it is not a full generated-source performance run and was not
sanitized for all sizes. The reproducible full generated mode remains unrun.

The only nonzero subprocess exits in the final run were the optional CPU query and
four deliberate `E_CAPTURED` frontend interception calls. No required check, build,
canonical execution, sanitizer, generated wrapper or paired measurement failed.

## Exact data costs

Each invocation has six allocations and six frees in lifecycle scope, and zero
allocations/frees in the timed reused scopes. Scratch is allocated once and reused
between the two stages. All cases finish with zero arena live bytes.

| Representation | Layout | Peak data bytes | Setup written bytes | Operation written bytes | Operation copied bytes |
| --- | --- | ---: | ---: | ---: | ---: |
| F64 | contiguous | 1,624 | 2,176 | 1,312 | 512 |
| F64 | padded | 3,296 | 3,848 | 1,312 | 512 |
| Complex F64 | contiguous | 3,248 | 4,352 | 2,624 | 1,024 |
| Complex F64 | padded | 6,592 | 7,696 | 2,624 | 1,024 |

For F64, the first pack copies/writes 192 bytes, generic regroup copies/writes
320 bytes, first GEMM writes 320 bytes and second GEMM writes 480 bytes. Complex
byte counts double. These are whole-schedule counters even in primitive timing
scopes; those scopes time only their selected operation. Setup includes sentinel
initialization and six source patches. Oracle checks and three native output
assertions add no writes. Arena counters exclude Lean/allocator internals and
BLAS-private allocations. RSS can include launcher pre-exec memory and is not an
isolated native heap measurement.

## Retained evidence

`evidence.tar.gz` contains 241 files (298,198 bytes), SHA-256
`b87d5d683eb58c3bfa632eba5a0b16bcbe09b5e578e14979280bf53ead1d149f`.
`archive-manifest.json` lists every included path, byte length and hash; all archive
members were rechecked against it. It includes source/runtime snapshots, generated
packages, wire/emission/wrapper files, commands, compile times, backend metadata,
raw rows, native validation and the independent cost audit. Plain metadata and
compressed raw/summary copies alongside it contain the same evidence for convenience.

`binary-inspection-manifest.json` preserves hashes for 40 excluded executables, debug-symbol or
large inspection files. Compiled Lake cache files are not retained. Exact native
code inspection remained available in the full local output directory; this compact
bundle does not embed those listings or executable binaries. Statistical summaries
are preserved without a speedup/parity claim. Logical checker/proof results,
finite native tests and performance acceptance remain distinct.
