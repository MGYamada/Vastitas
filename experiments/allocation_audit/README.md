# Allocation-only audit of generated resource calls

This experiment counts allocations at specific Lean FFI and emitted-C sites.
It does **not** measure performance, total Lean heap allocation, allocator backing
pages, process memory, or BLAS workspace. Instrumentation changes private copies.
The default schema-v2 run observes the **actual current production**
`vastitas_io_unit_success` helper, including its `lean_obj_once` initializer and
returns. The explicitly named `private_fresh` comparator replaces that exact
helper with fresh Unit results only in the private experiment copy.

The fixture is the actual publicly checked two-edge contraction tree used by
[contraction_trees](../contraction_trees/README.md): pack, GEMM, regroup, GEMM with
six caller-owned allocations. The default smoke covers real/complex and
contiguous/padded storage. Each fresh process first executes one generated
lifecycle, then an explicitly reused or complete-lifecycle sequence. The C path
uses the same physical layouts, arithmetic order and block-copy comparator.

## Run

```sh
cargo build --locked
lake -d lean-kernel build
python3 experiments/allocation_audit/run.py \
  --prefix /path/to/pinned-openblas --output /tmp/allocation-audit
```

The output directory must not exist. `--full` selects the twelve tree fixtures;
`--one-case` is a debugging option. Every normal variant first performs canonical
public check/build/run, then builds an instrumented wrapper from the exact kernel
emit response. Retained `Generated.lean`, `Main.lean`, `Emitted.c`, private FFI and
observer sources make the actual call path inspectable. Inputs and pinned headers
are hashed and checked for changes at the end. Build/runtime command logs retain
raw outputs. Any elapsed-time fields inherited from the tree probe are invalid
for performance comparison: the observer performs deliberately expensive scans.

The [original macOS smoke](results/2026-11-01-macos/RESULTS.md) and its independent
verifier remain unchanged. They describe the earlier **pthread prototype**, not
the production Lean-once helper. Current schema-v2 records identify their actual
production revision/dirty state and input hashes separately. Use the current
`verify.py` for schema-v2 directories/archives; use the original record's verifier
for the original record.

## Observer coverage

`audit.h` is included only in private native/numerical FFI copies and in the
emitted wrapper's C compilation. No Lean runtime or production source is patched.
The observer records:

- Each fresh FFI `lean_io_result_mk_ok` or `lean_io_result_mk_error` result object.
- The allocation inside the actual production Unit-success initializer and
  every actual returned use of that persistent object.
- Each arena external wrapper from `lean_alloc_external`.
- Direct `lean_alloc_ctor` calls in the emitted C, including loop setup/results
  and the `finally` fallback when a returned constructor is not exclusive.
- Final-reference releases through the instrumented caller's `lean_dec`,
  `lean_dec_ref` and `lean_dec_ref_known` sites, plus actual arena finalizers.
- The original native arena counters and completed-arena costs, separately from
  Lean objects. Completed-cycle totals belong to the phase in which the arena is
  deleted; they do not assert that all of its allocations occurred in that phase.

Object sizes come from the pinned public `lean_object_byte_size` API. They are
Lean object bytes, not malloc usable sizes or operating-system committed bytes.
The fixed 4,096-entry observer table performs no dynamic allocation and fails if
full, if an address is registered twice while live, or if an unexpected tracked
object survives the observation window. Instrumentation is single-caller, like
the underlying arena. The separate concurrency executable uses only atomic
initializer/use observations, not this pointer-table observer.

The initial process/argument-list/module setup is excluded because its objects
are consumed inside uninstrumented runtime code. The `cold` phase means the first
resource call **after** Lean/module initialization; it is not a measurement of
all process cold-start work or proof that the backend has not initialized a pool.
The later `setup`, `run` and `cleanup` phases retain the existing wrapper's explicit
hoisting. Marker/report IO results are classified as `control`; the final report
result is created after observation and is excluded.

Recursive allocations/frees inside Lean libraries, IO error payload strings,
external-class registration, mimalloc backing pages, allocator metadata, BLAS
workspace/packing, and OS mappings are not observed. The pointer table verifies
balanced final releases for the tracked fixture objects; it is not a general
heap/leak detector. Existing arena counters separately verify all data frees and
zero live arena bytes. This run does not replace ASan/LSan or native refinement.

## Actual production shared result and private comparator

The production helper constructs one result with
`lean_io_result_mk_ok(lean_box(0))`, explicitly calls `lean_mark_persistent`, and
publishes the object through the supported pinned `lean_obj_once` API. The
instrumenter requires the entire actual initializer/once/return envelope to
match. It observes allocation inside that initializer and the return after
`lean_inc`; it preserves actual publication and persistence. No raw object-layout
writes or replacement singleton are used. The one 16-byte object is intentionally
retained for process lifetime and counted. It holds no arena or error payload.

`private_fresh` is an experiment-only comparator, not a production build or the
old measured compiler. It replaces the exact helper envelope with a fresh
`lean_io_result_mk_ok(lean_box(0))` while leaving every caller and error check
unchanged. Both variants first build/run the unmodified public production
program; only their separate instrumented copies differ. `persistent.c` remains
as historical prototype source and is not compiled by the current default run.

All storage/GEMM operations and their error checks still execute. New-arena results
remain fresh because they carry an external object; errors remain fresh. The
shared result is nonexclusive. Consequently, the emitted `finally` cannot reset
and reuse `close`'s result constructor: it allocates its own result. This is
retained in the counts and emitted C, not subtracted as an incidental cost.

A separate executable compiles the actual production FFI with only an atomic
observation added after the initializer's `lean_mark_persistent`. Eight dedicated
Lean task threads rendezvous before their first helper call. Four fresh-process
executions check 8,000 successful uses plus a `finally` use after an actual native
handle error, exactly one initializer invocation, eight distinct TLS worker
identities and an unchanged persistent Unit payload. It also verifies that two
actual new-arena results, two stats results and two native error results are
distinct, exclusive and nonpersistent. The error propagates unchanged. These
tests call the real helper; they do not compile or count the pthread prototype.

The native failure fixture changes one expected output bit in the captured wire,
then passes that wire through the actual kernel checker/emitter again. The
instrumented wrapper must receive the exact `E_NATIVE_EXPECT` error, complete
`finally`, finalize the arena, free all six data allocations, and leave no
unexpected tracked object. It is a runtime-error test, not a source typing
rejection or an alternative semantic checker.

The result depends on the pinned API/toolchain and actual emitted caller code.
It is evidence for this implementation, not a proof of every client or platform.
Fewer observed allocations do not establish a speedup or the Fast like C gate.
