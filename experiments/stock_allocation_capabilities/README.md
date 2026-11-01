# Stock Lean allocation capabilities

This experiment calibrates what the **unchanged installed, pinned Lean runtime**
can observe. It adds no production hooks and rebuilds neither Lean nor OpenBLAS.
It compiles a small observer and collects three fresh-process records. There are
no timings and no claim of whole-process allocation coverage or Fast like C
acceptance. The earlier `/private/tmp` probe was preliminary; retained repository
records must identify their own measured source revision and hashes.

```sh
python3 experiments/stock_allocation_capabilities/run.py \
  --out /tmp/vastitas-stock-capabilities-new --cc cc
python3 experiments/stock_allocation_capabilities/verify.py \
  /tmp/vastitas-stock-capabilities-new
python3 -m unittest discover -s experiments/stock_allocation_capabilities -p 'test_*.py'
```

The explicit output directory must be outside the source checkout and must not
exist, even if empty. Run from any working
directory; the runner discovers Lean's prefix using the repository's toolchain
selection and checks the root/kernel pins. `--cc` is a compiler executable, not
shell text. The profile requires a 64-bit host. macOS and Linux follow the existing native convention of `LEAN_CC`
plus the installed prefix's `lib` search path. A changed Lean or allocator pin
requires deliberate API/header revalidation. The vendored MIT stats header is
verified against its exact upstream Git blob; it is missing from the installed
Lean headers despite the stock archive exporting the functions.

## Observations and limitations

The single probe mutator uses ordinary `lean_alloc_ctor`, `lean_alloc_sarray` and
`lean_dec`. It holds and releases 1,024 constructors and eight 2 MiB ByteArrays,
then creates/releases 10,000 small objects and 128 large objects between samples.
The visitor identifies each retained pointer and checks release, block counts and
allocator block-byte totals against `mi_usable_size`. Payload bytes, object header
bytes and allocator block bytes remain separate.

The eight snapshots are baseline, small held/released, large held/released,
small transient, large transient and an explicitly separate forced collection.
The observer warms its APIs and faults in its static snapshot buffers first.
It retains their byte cost in the output, allocates nothing in visitor callbacks,
prints only after all snapshots and creates its returned IO result afterward.
`LEAN_NUM_THREADS=0` prevents creation of the runtime task manager in the pinned
[initialization code](https://github.com/leanprover/lean4/blob/v4.35.0/src/runtime/object.cpp#L1097-L1121).
No other tasks/threads are created by the probe. The
[heap visitor](https://github.com/microsoft/mimalloc/blob/v3.4.5/src/arena.c#L2312-L2378)
assumes no other thread is running with that heap; this is not a concurrent
production monitoring API.

Keep the following channels **non-additive**:

| Channel | What it can establish | What it does not establish |
|---|---|---|
| Main-heap visitor | Tested retained addresses and live allocator block bytes at samples | Allocation churn, between-sample peaks, other heaps/allocators, arbitrary object types |
| Stock allocation counters | Only the count/path/size signals that calibration actually detects | Zero allocations when a disabled counter stays zero; universal coverage |
| Reserved/committed/pages and process RSS | Allocator backing and process diagnostics | Logical live objects or a quantity to add to live-block bytes |
| Backend workspace | Not measured in this experiment | OpenBLAS checkout, backing or OS allocation totals |

Normal-count deltas are classified as calibrated, unsupported/no signal, or
unsupported/inconsistent. The same classification is independently applied to
the large-object count. A huge `current` field that stays unchanged after known
objects disappear is explicitly **not live bytes**. An apparently matching
release only calibrates this test; it is not a general peak or refinement theorem.
Missing phases, altered domains and unsupported-to-zero claim substitutions are
verification errors. Neither normal nor huge unsupported counters fail a valid
capability record merely for being unsupported.

## Pinned source explanation

Lean [pins mimalloc v3.4.5](https://github.com/leanprover/lean4/blob/v4.35.0/CMakeLists.txt)
and compiles its allocator with the small-object entry point in
[one translation unit](https://github.com/leanprover/lean4/blob/v4.35.0/src/runtime/mimalloc.cpp).
The fast path is inlined, so exported `mi_malloc` or system `malloc` interposition
does not cover all Lean objects. Exported statistics APIs alone do not establish
that the counters were enabled.

The pinned [release flags](https://github.com/leanprover/lean4/blob/v4.35.0/src/runtime/CMakeLists.txt)
and [defaults](https://github.com/microsoft/mimalloc/blob/v3.4.5/include/mimalloc/types.h#L72-L87)
select `MI_STAT=0` unless overridden. At that setting,
[normal allocation accounting](https://github.com/microsoft/mimalloc/blob/v3.4.5/src/alloc.c#L66-L76)
is disabled, but [huge-page allocation](https://github.com/microsoft/mimalloc/blob/v3.4.5/src/page.c#L924-L945)
increments huge bytes/count unconditionally. Corresponding
[deallocation accounting](https://github.com/microsoft/mimalloc/blob/v3.4.5/src/free.c#L650-L677)
is disabled, including huge decrements. Thus huge `current`/`peak` can remain
cumulative after release; that is not evidence of a leak. The runner records
the actual binary's behavior rather than assuming build flags from source alone.
`upstream-sources.json` retains the inspected source URLs and Git blob IDs.

## Evidence format

`record.json` names all three raw JSON streams, parsed observations, independently
reconstructed classifications, source snapshots, toolchain fingerprints and
command logs. Its complete file inventory includes emitted C, object files,
observer binary, repository inputs, all installed `include/lean/*.h` headers and
stdout/stderr for compilation, linkage and execution. The installed Lean/Lean C
driver/runtime archive are hashed before and after, not rebuilt or embedded.
System SDK/libc sources are external toolchain dependencies, not vendored inputs.
The observer inherits the ordinary system environment except the recorded
compiler and zero-worker overrides; it is not a hermetic runtime build.

The independent verifier checks hashes, exact file/run/phase coverage, raw/parsed
agreement, known retention/release arithmetic, domain types and claims. It accepts
a directory or ZIP without extracting it. An archived record is immutable;
later reports identify the measured feature revision separately from the commit
that adds the record. A hash inventory detects corruption, not maliciously
rewritten experimental evidence or native-runtime correctness.

Complete attribution still needs independently calibrated generated/FFI event
coverage and backend workspace/backing channels. OpenBLAS's pool checkout and
release need not allocate/free OS backing. A future diagnostic `MI_STAT=2` runtime
could expose more churn, but its counts must not be called stock-production
evidence. Valgrind or malloc interposition alone does not prove completeness.
These capability checks require no controlled timing host and do not waive the
remaining performance gate in [the completion ledger](../../docs/stage1-completion.md).
