# OpenBLAS workspace lifetime observation

This optional diagnostic experiment separates a **borrowed pool capacity** from
the **backing requests retained after return**. It rebuilds the pinned OpenBLAS
0.3.34 release twice in one scratch tree: first unchanged, then with hooks in
`driver/others/memory.c` alone. Each run checks its complete object inventory and
requires every object except `memory.o` to remain identical. This is an
instrumented backend experiment, not unchanged production
allocation evidence, a timing benchmark, source authority or native refinement.

The normal compiler, runtime and numerical adapter are unchanged. The probe links
the actual native storage, diagonal and GEMM adapter sources to each archive.
There is no Lean compiler/runtime in these probe executables. Later integration
with generated-source lifecycles remains a distinct measurement obligation.

## Run

```sh
python3 experiments/openblas_workspace/run.py \
  --out /tmp/workspace-record-new --build-dir /tmp/workspace-build-new \
  --archive /path/to/OpenBLAS-0.3.34.tar.gz --jobs 4
python3 experiments/openblas_workspace/verify.py /tmp/workspace-record-new
python3 -m unittest discover -s experiments/openblas_workspace -p 'test_*.py'
```

Both directories must be new, separate and outside the checkout. The build
directory retains extracted sources, stock/diagnostic installed prefixes and
objects for inspection; it is **not** part of the compact evidence record.
Omitting `--archive` downloads the SHA-256-pinned release used by
[`build_openblas.py`](../../scripts/build_openblas.py). `--cc` is one compiler
executable. Linux CI explicitly selects `--target HASWELL`; macOS uses host
detection. The options retain sequential, locking, static LP64 BLAS without
Fortran or LAPACK. The experiment builds the upstream `libs` target, not the
upstream full test suite. Its own fixtures run both linked libraries.

The runner clears inherited Make/compiler/preload switches, records its selected
environment, compiler, host, actual library configuration, build/link commands,
archive/binary/object hashes and exact sources. This does not make the system SDK,
compiler, libc or operating system hermetic. Three fresh processes for each
variant and case produce **150 executions / 75 pairs**: one calibration and
24 adapter cases per variant, repeated three times. Cases cover real/complex,
square extents 0/2/32/256, left N/T/C, offset/padded column-major layouts, two
overwrites followed by accumulation, unchanged inputs/padding, and a rejected
alias/invalid-operation preflight. No elapsed-operation times are collected.

## What is observed

The private patch requires the exact release `memory.c` SHA-256
`3b5bedc19c4555de21fb0c649177d9be1545d28fc61a8cbcc475e4a9bffc9935`.
Only the two conditional definitions of each pool/direct allocation, return and
shutdown entry are renamed. Calls retain their public names, including calls
from the same translation unit's constructor. This avoids the missing internal
calls possible with external-symbol-only interposition. All direct `malloc`,
`free`, `mmap` and `munmap` calls in that exact file are separately observed.
Compile-time guards reject threaded/TLS/ILP64 or alternative backing allocators.

Events preserve their phase, address, size, result and failure errno. Fixed static
storage holds at most 4,096 events and allocates nothing in callbacks. A second
observed thread, overflow or observation after the final report terminates the
probe. The sequential fixture does not create additional threads. Reported
observer bytes are the sum of the explicitly declared mutable objects' `sizeof`
values, excluding linker alignment, read-only strings, code, stack and libc's
reporting allocations. These bytes are overhead, not backend workload storage.

The observer starts before library constructors. Phase 0 therefore retains Linux
warmup allocations and any alignment-related prefix/suffix unmaps; macOS may have
no startup pool event. Phase 10 is fixture setup after initialization, phases
11–17 identify calls/returns, and phase 18 explicitly calls `gotoblas_quit`.
That function both releases backing and disables its later destructor. Calling
`blas_shutdown` alone before the normal destructor would not provide that
lifecycle. There are no backend operations after phase 19's final marker/report.

The calibration holds two distinct pooled buffers, returns one, checks reuse of
the same address, then returns both. A separate direct/no-lock allocation tests
the malloc/free channel. Every active pool loan must fit known live backing.
The independent verifier replays partial unmaps, detects overlap, unknown/double
return/free, release of borrowed storage, missing constructor evidence and
unreleased backing at quit. It reconstructs input/output checksums from an
integer coordinate oracle (period-15 inputs), verifies all padding and compares
stock/diagnostic outputs, costs and configurations. Computed zero results have
their sign canonicalized in checksums; input and padding words are unchanged.
It also reconstructs the
allowed source patch and verifies that only `memory.o` changed. These checks
detect corrupt/inconsistent records; hashes are not authenticity certificates.

| Channel | Meaning | Exclusions |
|---|---|---|
| Borrowed capacity | `BUFFER_SIZE` per active pooled/direct loan | Actual bytes populated by GEMM or read/written by packing kernels |
| mmap backing | Page-rounded address ranges requested by this `memory.c`, including transient alignment overmapping and later retained pool capacity | RSS, committed pages, page faults or mappings inside libc/other files |
| malloc backing | Requested bytes from this `memory.c`, including direct-buffer alignment allowance | Allocator usable size, internal malloc backing/metadata and other allocation sites |
| Arena data | Existing adapter peak data bytes, checked independently | Backend pool, Lean objects and full process memory |
| Observer | Explicit mutable diagnostic storage | Native operation cost or a value to subtract from a production timing |

These are overlapping or differently scoped channels and must not be added into
a purported total heap figure. Returning a pooled buffer can leave all its
backing retained; borrowing it again need not allocate. A zero pool-event count
does not establish zero workspace: an architecture's small-matrix path can use
other storage. This experiment does not count actual BLAS packing/copy bytes,
kernel stack/local storage, other OpenBLAS files, libc/OS internals, Lean objects,
between-callback residency peaks or process-wide allocations. It deliberately
does not force `NO_WARMUP` or disable the actual small-matrix implementation.

## Evidence and acceptance boundary

`record.json` inventories every compact record member: raw stdout/stderr, parsed
events, source snapshots including the release license and original/patched
memory code, generated configuration/installed headers, all object hashes, linked
probe binaries, commands and actual environment. Full backend archives are
fingerprinted, not embedded. The verifier accepts a directory or ZIP without
extracting or executing archived code. The scratch build tree is separate.

The replayer's mutation tests include missing startup backing, double/unknown
returns, overlapping loans, premature unmapping, partial unmap gaps, failed
allocations, truncated records, changed capacity units and unfinished shutdown.
Native production sanitizer/Valgrind checks remain separate. The new diagnostic
counts neither replace those tests nor establish a formal native memory theorem.

The [Stage 1 completion gate](../../docs/stage1-completion.md) remains open for
complete allocation/peak-memory/backend cost attribution and representative
generated workloads, as well as controlled-host equivalent-C timing and a
predeclared tiny-call budget. A dedicated host is unavailable; instrumenting a
backend does not relax those conditions.
