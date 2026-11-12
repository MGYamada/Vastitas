# Storage and ownership

This chapter states the model of storage that Vastitas programs and their
compiler follow. It says what an allocation, a view and a loan are, which
accesses may coexist, when memory counts as initialized, and what a numerical
operation may cost. [Resource programs](storage/resource-programs.md) gives
the statements that programs write, and the numerical chapters give the
operations on maps.

The model is wider than the source syntax. Its rules state required behavior
of the compiler, of its intermediate representation and of every lowering. A
rule on a construct that has no statement binds the design of that construct.
In this chapter, **must** therefore binds the compiler and its measurements as
well as programs. A rule that begins "By design" states a design target: a
change must meet it or record the departure as an unresolved gap. A rule is
not evidence that the compiler meets it. An implementation note says what the
compiler implements.

This chapter gives no diagnostic codes and no examples. Each section names
the sections of [Resource programs](storage/resource-programs.md) and of the
numerical chapters that hold the rules on programs for its subject, with the
code of each error and with tested examples.
[Independent checking and proof boundary](internals/resource-checking.md#independent-checking-and-proof-boundary)
holds the requirements on the compiler that concern its wire protocol, its
repeated checks and its proofs. The other chapters on
[resource checking](internals/resource-checking.md) describe how the compiler
checks these rules and what is proved about its checks.

## Performance contract

### Fast like C

**Fast like C** is the performance and architecture goal of Vastitas, and it
has the highest priority among its design goals. It names a C/C++-class target: mathematical
abstraction must admit native code with the storage access, allocation
behavior and kernel calls of a competent C implementation of the same
computation. Performance is a design constraint from the representation
boundary onward. It is not an optimization project that waits until the public
interfaces are fixed.

Correctness, declared mathematical meaning and explicit numerical policy
constrain the comparison. A faster program that drops an ownership check does
not meet the goal. Neither does one that changes arbitrary-precision integers
into machine integers, or one that silently changes floating-point semantics.

The goal does not assert that programs reach the performance of C. Compiler
latency and the run time of generated programs are separate measurements.

Rules:

- When a safe design is too expensive, its representation or its interface
  must change and be measured again. A different computation must not be
  certified in its place.
- Every numerical operation must expose a cost contract: reads, writes,
  allocation, copies and packing, retained bytes, synchronization, and
  validation that depends on data.
- By design, static identity, type, dispatch and authority evidence disappears
  from the hot loop once its obligations are discharged. Required dynamic
  dimensions, bounds and lifetime information remain until their last
  justified use.
- Every completion claim must record its measured comparisons with C and its
  unresolved gaps. Comparisons for reverse passes belong to the completion
  claims of reverse passes.

### Performance evidence and acceptance

A comparison measures a Vastitas program against a **baseline**, a competent
C implementation of the same computation.

Rules:

- The baseline must use the same algorithm, scalar representation, layout,
  backend and backend version, thread count, numerical policy and contract of
  inputs and outputs. A comparison of exact integers must use an equivalent
  arbitrary-precision implementation.
- A naive triple loop is not the baseline for a Vastitas call of optimized
  BLAS.
- The comparator of the gate must stand alone. It must use ordinary allocation
  and direct backend calls. Its primary timing loop must have no Vastitas
  arena preflight, no checks of the backend configuration per call and no
  cost counters.
- A separate measurement in C with the arena must locate the overhead of the
  runtime against that of code generation. Ratios between generated code and
  that measurement cannot establish the gate.
- The logical costs of the comparator must be replayed in a separate
  diagnostic build. A timing cost field that was not observed must stay
  blank; it must not be reported as zero.
- A measurement must cover both the execution of the prepared kernel and the
  full operation, including allocation, preflight and packing.
- A measurement must include the checks that each implementation requires.
  The baseline must not repeat dynamic checks that only Vastitas needs, and
  Vastitas checks must not be hoisted out of the timed scope to obtain parity.
- A record must hold the revisions of source, intermediate representation and
  native code, the generated code, the C source and the compiler flags. It
  must also hold the CPU, operating system, allocator, backend, thread
  configuration, sizes, input generation, warmup and raw samples.
- The order of measurements must alternate, and a report must give
  distributions and uncertainty.
- Results and observable outputs must be checked, so that the elimination of
  dead code cannot erase work.
- The sizes must include sizes that fit the cache, sizes bound by memory, and
  the edge cases of zero size and of strides.
- Unexpected allocation, hidden copies or asymptotically greater data movement
  fail the cost contract, even when one timing sample is favorable.
- Correctness CI on both operating systems is mandatory. Noisy hosted timing
  alone is not a performance gate.
- A budget must not be widened silently to accommodate a regression. The cause
  must be resolved, or an explicitly reviewed change of target recorded.
- A path that is unmeasured or materially slower remains a performance gap,
  and it blocks the corresponding completion claim.

The [plain-C harness](https://github.com/MGYamada/Vastitas/blob/main/experiments/plain_c/README.md)
supplies the stand-alone comparator for the finite public GEMM, packing and
contraction-tree profiles.

| Workload | Required evidence |
| --- | --- |
| Elementwise and strided access, transpose views | Run time, bandwidth, validation count, allocation and copy count |
| Real and complex GEMM; transpose against adjoint | Run time by size, identical backend, adapter overhead, correctness |
| Repeated reuse of destination and scratch | Zero unexpected allocation per call, stable peak of live bytes |
| Finite contractions and explicit packing | Total run time, intermediate bytes, packing bytes and time, deterministic schedule |
| Small calls | Batched measurements, absolute overhead and distribution; not only unstable ratios |
| Retain, snapshot and recompute in reverse passes | Forward and backward run time, peak of retained bytes, copy bytes and replay count |

The engineering target for representative bulk workloads that take at least
1 ms per sample is a median slowdown of at most 10% against equivalent C on a
controlled host. This is a provisional acceptance budget. It is not a claim of
measured results or a universal theorem. The paired samples and their
uncertainty must be published. A noisy result that crosses the budget is
inconclusive: it requires measurement and is not a pass. For tiny calls, an
absolute overhead budget must be set and recorded before they are accepted.

> **Implementation note.** The acceptance of this section on a controlled
> host is open. [Implementation status](internals/resource-checking.md#implementation-status)
> records what is implemented and measured.

## Identities and rights

| Layer | Identity and right | Does not imply |
| --- | --- | --- |
| Mathematical object or value | Nominal object, base, basis, scalar and logical version | A particular layout or writable memory |
| Physical allocation | Fresh allocation identity, size, allocator and live lifetime | Equality of mathematical endpoints |
| Storage access | Region, initialized cells and read or write loan | Function-edit authority or rights to wire a graph |
| Network occurrence | Fresh occurrence and linear port identities | A fresh allocation or disjoint tensor factors |

Rules:

- Function-edit ownership is the independent discipline of
  [edit authority](language/edit-authority.md). Borrowing a function does not
  borrow its data.
- Two occurrences of one immutable tensor have fresh ports. They are not
  copies.
- The runtime may share immutable descriptors. Copying a descriptor grants no
  mutable authority.
- A numerical logical value may reuse storage only after every dependency on
  its previous contents has ended or has been retained explicitly.

[Storage types](storage/resource-programs.md#storage-types) gives the rules
of owners and loans, [Spaces and bases](linalg/maps-and-gemm.md#spaces-and-bases)
those of the identities of spaces and bases, and
[Two-map networks](linalg/networks-and-packing.md#two-map-networks) and
[Contraction trees](linalg/networks-and-packing.md#contraction-trees) those of
occurrences and ports.

## Allocation and layout records

An owned allocation records a fresh identity, a live generation, an element
representation, a byte capacity, a required alignment, an allocator and its
deallocator, a device or address space, and an initialization map. A view
retains the identity of its allocation and a checked layout descriptor: byte
offset, rank, length of each axis, byte strides, element width, access mode
and region. For indices `0 <= i[k] < length[k]`, the accessed byte interval
begins at `offset + sum(i[k] * stride[k])` and has the width of the element
representation. The resource profile admits views of finite rank, with scalar
elements of positive width and nonnegative strides.

Rules:

- A reused address must receive a fresh identity. Equal pointers are not
  sufficient provenance of an allocation.
- The checker reasons with mathematical integers. Machine lowering must
  establish that every size, multiplication, addition and pointer conversion
  is representable.
- Negative strides, packed bits and foreign device memory need separately
  specified extensions. The checker must reject them where they are not
  supported.
- A read-only broadcast view with zero strides may be represented explicitly.
  A writable view must be injective over its logical indices, with element
  byte intervals that do not overlap. A zero stride on an axis longer than
  one fails this.
- The accessible intervals must lie within the capacity and satisfy the
  alignment of the element.
- A view with an axis of length zero has no accessible element, and no element
  pointer of it may be dereferenced. Its metadata must be validated without
  evaluating a length minus one in an unsigned machine type, and without
  forming an out-of-bounds pointer.
- Capacity, padding and initialized logical cells are distinct. Padding is
  never read.
- A dense matrix of the resource profile uses column-major storage with an
  explicit leading dimension `ld`. For an `m x n` matrix that has an element,
  `ld >= max(1, m)`, and the capacity covers its last element, including
  column padding.
- Narrowing to LP64 must be checked before entry into BLAS.
- The adapter ABI fixes complex storage and alignment. Neither is inferred
  from the source spelling `Complex<F64>` or from an unchecked cast of a host
  struct.
- Transposition and reborrowing do not authorize reinterpreting half of a
  complex element. An empty view forms no pointer.

[Storage types](storage/resource-programs.md#storage-types) gives the rules
of layouts and of the sizes of allocations with their codes.

> **Implementation note.** The checker records for an allocation its identity,
> owner, element type, capacity in bytes, initialization and a version. It has
> one allocator, one address space and one alignment per element type. Its
> views are the rank-two layouts of
> [Storage types](storage/resource-programs.md#storage-types): a byte offset,
> stored rows and columns, a leading dimension and a transposition flag. A
> tensor of rank three is a grouping of axes over such a rectangle, as
> [Networks, packing and contraction trees](linalg/networks-and-packing.md)
> describes. The offset of a view with a cell is a multiple of 8 bytes for
> `F64` and of 16 bytes for `Complex<F64>`; pointer alignment is 8 bytes for
> binary64 components. The checker requires `ld >= max(1, m)` for an empty
> view too. It rejects strides other than the leading dimension and broadcast
> views with zero strides.

## Regions, overlap and alias evidence

A **region** is a set of accessible byte intervals in one allocation. A view
covers a region. An access is **active** while its loan is
[live](storage/resource-programs.md#resource-functions) and not suspended.

Rules:

- Different live allocations are disjoint. Within one allocation, only
  independently checked layout or partition evidence establishes disjoint
  regions. Equal shapes, different variable names, tensor factors and distinct
  mathematical bases do not.
- A checker may accept contiguous intervals, and explicit partitions whose
  sizes, offsets and coverage it can reconstruct.
- Strided access may use a conservative enclosing interval. When that interval
  overlaps another access, the checker must reject the conflicting loans
  unless supported partition evidence proves them disjoint.
- A check on the hot path must not enumerate every tensor element to resolve
  aliasing.
- The checker treats unknown overlap as overlap for mutable access. No
  implicit defensive copy repairs it. The caller may request a copy or a
  packing operation, supply partition evidence that the checker supports, or
  choose a schedule in which the loans are not live at once.
- Two accesses that are active at once may overlap when both are reads. A
  write must not overlap a read or another write that is active at the same
  time, including an access through another view of the same cells.
- A backend alias attribute such as C `restrict` needs a translation argument
  for its entire access scope. Pairwise checks at one instruction do not
  authorize stronger alias promises for a surrounding function. Without the
  argument, the attribute must be omitted: an invalid native alias contract
  must never buy speed.

[Resource statements](storage/resource-programs.md#resource-statements)
gives the rules of overlapping loans and of child loans with their codes.

> **Implementation note.** The checker compares, for each view, the byte
> interval from its first cell to its last. Views whose intervals are disjoint
> are compatible. Views whose intervals overlap conflict, even when their
> cells are disjoint, as two rows of one matrix are.
> An empty static view conflicts with nothing; a runtime loan covers its whole
> allocation and conflicts even when it is empty. No partition evidence is
> implemented.

## Ownership and explicit transitions

The resource environment tracks each owner, each live loan and the state of
each region. These operations must be represented and independently checked:

| Operation | Required state | Result |
| --- | --- | --- |
| Allocate | Checked size and alignment, and a successful allocation | One live owner; uninitialized region |
| Move | Live owner; no live loan in the resource profile | Fresh owner binding; the old binding is unusable |
| Read loan | Live storage; requested cells initialized; no overlapping writer | Shared read access for a bounded scope |
| Write loan | Live owner; no overlapping active access | Exclusive access, in an explicit write-only or read and write mode |
| Return loan | Matching live loan, and all children returned | Access ends; initialization and changes pass to the owner |
| Drop | Live owner, no live loan and no retained dependency | Exactly one release by the matching allocator |

Rules:

- An exclusive parent may be split or reborrowed only with an explicit child
  region inside the parent and with checked compatibility between siblings.
- While a child is live, the access of its parent is suspended. Children
  return from the inside out. Shared children do not permit their exclusive
  parent to write.
- Storage authority is separate from edit delegation. The two mechanisms must
  not share tokens because names match.
- A loan must not escape through a function result, an existential package, a
  retained descriptor or other data. The one exception is an escape that an
  explicit lifetime contract of the result and an audit of the caller permit.
- An owned result transfers its owner explicitly.
- A last use may shorten a loan only when the checked resource schedule
  records that shortening.

[Resource statements](storage/resource-programs.md#resource-statements)
gives the rules of `allocate`, `move`, `borrow`, `release` and `drop` with
their codes, [Resource functions](storage/resource-programs.md#resource-functions)
those of owned results and of the end of a body, and
[Scalar values and calls](storage/resource-programs.md#scalar-values-and-calls)
those of calls.

> **Implementation note.** No lifetime contract for results is implemented:
> the checker rejects every escaping loan. No schedule shortens a loan. A loan
> that a program borrows ends at its `release`. A loan that a call receives
> ends for the callee when the call returns, and the loan of the caller
> resumes. A loan that the compiler creates for one statement ends inside
> that statement. The checker implements no retained dependency in the sense
> of the row "Drop" of the table. The one dependency that it records is that
> of a [cache](linalg/networks-and-packing.md#caches) on the allocations of
> its packing. A cache keeps no allocation alive: the checker accepts a
> `drop` of such an allocation, and the `drop` ends the validity of the
> cache.

## Initialization, branches and failure

Initialization is tracked by region, not by one flag on an allocation.

Rules:

- A write-only loan may cover uninitialized storage. Any read needs
  initialized cells. A partial write initializes only its checked write set.
- Moving an owner preserves the state of initialization. A program must not
  read padding or an unwritten part of a view.
- At the join of a branch, ownership and live loans must agree after explicit
  normalization. An owner that one arm moved is not silently live after the
  join.
- The region that is initialized after a branch is the intersection of the
  regions that its arms initialize.
- Different fresh results of the arms need an explicit owner result binding.
  Equal sizes never make two allocations, or two nominal mathematical
  identities, the same.
- Every admitted exit path must release or return each of its resources
  exactly once.
- Before the first external write, an operation must validate shapes, nominal
  endpoints, layouts, aliasing, initialization, arithmetic narrowing and
  backend support, and it must complete every required scratch allocation. A
  failure in this **preflight** preserves the output.
- Preflight is not a transaction guarantee for a native crash, a cancellation
  during a kernel, a hardware failure or a backend that violates its contract.
- A fallible operation that has started to write must expose its partial state
  or invalidate the affected output. It must not return an initialized
  success value.
- An operation that needs all-or-nothing publication must use explicit staging
  storage and a commit, and its cost contract carries that extra storage and
  copy.

[Resource statements](storage/resource-programs.md#resource-statements)
gives the rules of initialization with their codes,
[Scalar values and calls](storage/resource-programs.md#scalar-values-and-calls)
those of branches, and
[Running a resource program](storage/resource-programs.md#running-a-resource-program)
those of a program that stops. [Matrix products](linalg/maps-and-gemm.md#matrix-products)
states the preflight of a product.

> **Implementation note.** A branch has no owner result bindings: an owner
> that an arm allocates ends in that arm. No operation with staging storage
> and a commit is implemented.

## Views, transpose, conjugation and packing

A view changes metadata and access rights and keeps the provenance of its
allocation. A transpose permutes the axes and their strides. As a view it
allocates no buffer. **Packing** is the copy of the cells of a view into
another layout, which a backend may need; a packing step is explicit, and its
target is storage that the plan names. An adjoint also conjugates complex
elements.

Rules:

- A logical conjugated read view is not a writable raw pointer with the same
  meaning.
- The lowering may use a transpose flag or a conjugate-transpose flag that
  the BLAS backend supports, after it has checked the descriptor contract of
  that flag.
- A layout that the backend does not support needs an explicit packing step,
  with its axis order, destination layout, byte count and lifetime in the
  plan.
- A contraction of high rank records both its grouping of axes and its
  permutation before GEMM.
- A reshape is a view only when the byte mapping and the contract of the
  mathematical indices justify it. Otherwise its materialization is explicit.
- No high-level operation silently introduces copy-on-write, reference-count
  traffic per element, a layout conversion or a temporary whose size is
  proportional to the input.
- An operation may allocate when it declares the allocation, and the
  allocation must be visible in the checked plan. Several references to
  immutable data demand no copies of elements.
- The provenance of a view must not be erased because the native operation
  accepts pointers.

[Resource statements](storage/resource-programs.md#resource-statements)
gives the rules of `transpose`,
[Transformed maps](linalg/transforms-and-metrics.md#transformed-maps) those
of dual, conjugate and adjoint maps, and
[Packing and contraction](linalg/networks-and-packing.md#packing-and-contraction)
those of packing.

> **Implementation note.** No reshape as a view is implemented. The
> statements `pack3` and `regroup` of
> [Networks, packing and contraction trees](linalg/networks-and-packing.md)
> materialize a regrouping of axes explicitly.

## Destination passing, scratch and local mutation

A **destination** is storage of the caller to which an operation writes its
result. **Scratch** is storage that an operation uses for intermediate
values, and that holds no value of the program after the operation.

Rules:

- Operations must support destinations that the caller provides, and reusable
  scratch with explicit ownership.
- By design, the fast path of a numerical kernel performs no heap allocation
  after a successful preflight when its caller supplied compatible output and
  workspace.
- Stack allocation, scalar replacement and fusion are choices of
  representation only while the obligations of lifetime, initialization,
  aliasing and meaning remain valid.
- Scratch has requirements of size and alignment and an explicit lifetime
  that ends before reuse. Uninitialized scratch is not a source operand.
- Pooling must retain allocator provenance and establish that every loan and
  every residual dependency has ended.
- By design, layout and alias checks that do not vary in a loop belong to the
  enclosing checked operation. They are not repeated for every scalar element.
- Local mutation may realize a pure logical operation when no observer and no
  future residual needs the old value. A storage-safety theorem alone does
  not prove this refinement.
- Explicit resource transitions must stay distinct from the pure Core, and
  each supported lowering needs a proof of its connection to logical
  evaluation.
- The schedule of the resource profile is deterministic. A search for
  optimizations is not a prerequisite.

[Map parameters](linalg/maps-and-gemm.md#map-parameters) gives the rules of
a destination that a function receives,
[Pairings](linalg/transforms-and-metrics.md#pairings) those of the scratch of
`hermitian_diagonal`, and
[Contraction trees](linalg/networks-and-packing.md#contraction-trees) and
[Caches](linalg/networks-and-packing.md#caches) those of the buffers of a
plan and of the reuse of a packing.

> **Implementation note.** The
> [packing cache](linalg/networks-and-packing.md#caches) supplies one
> bounded reuse contract: the versions of source and scratch after packing,
> explicit invalidation and lexical cleanup, followed by the checked tensor
> contraction. Its versions cover whole allocations and every join
> invalidates, which is conservative. Its dependency metadata is erased before
> native execution. General pooling and retained evidence are not
> implemented.

## The GEMM contract

The GEMM profile uses `F64` and `Complex<F64>`, column-major LP64 storage, a
synchronous CPU and the explicit policy `NativeFast`. Its backend is OpenBLAS
behind a thin C adapter; [Numerical builds](guide/cli.md#numerical-builds)
gives the pinned version. `overwrite` is logically `C := alpha * A * B`, and
`accumulate` is `C := alpha * A * B + beta * C`. Each coefficient is 1 when
the operation gives none.

Rules:

- The common preflight validates scalar representation, endpoints and bases,
  dimensions, transpose and adjoint flags, leading dimensions, capacities and
  the compatibility of loans.
- The output must not overlap either input. Read-only inputs may share storage
  only when the contract of the adapter and of the backend permits it. No
  implicit copy repairs an alias.
- `overwrite` must never read the old `C`, and it accepts an uninitialized
  output. `accumulate` needs an initialized output.
- The read sets and write sets of the two modes differ in the checked
  intermediate representation, even where one backend call shape serves both
  with a coefficient. The write-only behavior of the native adapter must be
  trusted explicitly and tested; a mathematical zero multiplier alone does
  not establish it.
- For an empty output, `m = 0` or `n = 0`, the operation performs no element
  access.
- For an output with a cell and `k = 0`, `overwrite` must initialize the
  output to zero, and `accumulate` must leave `beta * C`, which preserves the
  output when `beta` is 1. The initialization contract of `accumulate` still
  holds.
- The adapter must specify these cases; it must not rely on undocumented no-op
  behavior of a backend.
- Overflow of dimensions and strides must be tested before any narrowing and
  before any write of the output.
- Nonfinite values and rounding must be checked against the declared
  `NativeFast` policy. Resource validity certifies no identity of real numbers
  and no bitwise portability.
- Numerical CI uses one backend thread. Programs without numerical operations,
  and the compiler itself, must remain usable without OpenBLAS.

[Matrix products](linalg/maps-and-gemm.md#matrix-products) gives the rules of
the `gemm` statement with their codes and an example, and
[Runtime maps](storage/resource-programs.md#runtime-maps) those of
`runtime_gemm`.
[Building a numerical program](linalg/maps-and-gemm.md#building-a-numerical-program)
says which programs need OpenBLAS.

## Residual retention

Residual retention is an obligation on the design of every reverse pass.
Here a **residual** is saved data for a later run of a
pullback. It is not the error estimate of a numerical solver. Exclusive
rights to write cannot prove that overwriting a primal value is safe for a
later backward computation. For example, the backward computation of
`y = x * x` needs the old `x`. Overwriting its uniquely owned buffer with `y`
is safe for aliasing, but it does not preserve that dependency.

Each required value must have one explicit retention strategy:

| Strategy | Permission and cost |
| --- | --- |
| Retain | Keep an immutable loan or dependency alive; overlapping mutation and release are forbidden |
| Snapshot | Copy to separately owned storage before mutation; record bytes and lifetime |
| Recompute | Retain sufficient inputs and a checked replay plan, including rule and policy dependencies; charge the recomputation |

Rules:

- A residual records the logical value versions that it needs, allocation
  identities and regions, revisions of rules and functions, basepoints, and
  numerical and evidence dependencies. Views retain the same
  dependencies.
- A saved pointer without a live dependency retains no value. Validity is
  checked before use; a name does not establish it.
- Recomputation must reproduce the value contract that the selected pullback
  requires. Effects, randomness, changed parameters, unstable numerical
  factorizations and a different execution policy are not replayable because
  a function has a signature that looks pure.
- Where the equivalence of a replay is unavailable, the plan must retain or
  snapshot explicitly. A checkpointing planner implements this contract; it
  is no reason to omit dependencies.
- A one-shot residual is consumed once. A reusable pullback needs a separate
  contract for a reusable residual, with stable shared inputs and explicit
  workspace on each call.
- Freezing dependencies may preserve a first derivative and break higher
  derivatives. Reverse passes of higher order must retain differentiable
  primal and residual dependencies, as
  [ADR 0001](adr/0001-mathematics-first-stdlib.md) requires.
- The plan must retain the old value, snapshot it or justify a replay. The
  checker must reject a stale residual, even when the later value has the
  same type.
- Geometric and numerical descriptors that carry invariants follow the same
  rule on dependencies.

[Reverse-pass primitives](language/smooth-declarations.md#reverse-pass-primitives)
gives the rules of the reverse passes that programs write.

> **Implementation note.** No reverse pass is backed by storage, so the rules
> on allocations, regions and loans have no instance.
> [Compiled reverse Core](appendix/glossary.md#compiled-reverse-core) meets
> the contract without storage. Its
> [residuals](appendix/glossary.md#residual) are points of smooth affine
> objects: immutable pure Core values that hold no allocation, region or loan,
> so no mutation can make them stale. A saved site uses Retain: its forward
> Core binds every residual, and its backward Core reads the bound values. The
> map value of an opaque step is retained in the same way. A recomputing site
> uses Recompute. Its backward Core receives the input point and evaluates
> again, along the same checked maps, the images that its steps read. Its
> opaque steps run the runtime reverse pass in recomputed mode, which keeps no
> tape. Exact rational evaluation of a polynomial map has no effect and no
> policy choice, so the replay reproduces each value. A pure value has one
> version, and the derivative rules belong to the closed primitive registry,
> so a residual records no value versions or rule revisions. Snapshot and the
> invalidation checks of this section do not arise.
>
> The encoding of a residual has a cost that this contract does not bound, and
> nothing measures it. Each image is an evaluated point: a fresh program node
> that holds one constant polynomial per coordinate. Every step that reads a
> point evaluates that node again to recover its coordinates as a fresh list
> of rationals. Each intermediate point is therefore read three times: by the
> next forward step and by the two backward steps around it. Each Jacobian
> step also allocates one list per table column. It checks its seed against
> its output point although the previous step produced the seed over that
> point, so the check cannot fail after the first step. The input point r₀ is
> bound as the point operand, so each step that reads a composite point
> evaluates it again. An equivalent C program keeps the coordinates of each
> point in registers or on the stack. Residuals as coordinates are not
> implemented; this is a recorded performance gap.

## Tensor ports and execution scheduling

Rules:

- Every occurrence creates fresh ports. Every finalized port is connected
  once, or returned at the boundary under its structural contract.
- Two occurrences may read one immutable tensor. The checks of wiring are
  independent of allocation loans.
- Acting on `V` and on `W` in one dense buffer of `V ⊗ W` may touch all the
  same entries. Rights on factors and mathematical commutation do not
  establish disjoint writes.
- A finite network lowers through a deterministic contraction order with
  explicit lifetimes of intermediates, output and scratch. Each contraction
  must pass the same storage audit as a direct call.
- No implicit copy, metric or conjugation may repair a conflict of wiring or
  of memory.
- Asynchronous execution and device transfers need profiles with explicit
  contracts of completion and lifetime.

[Two-map networks](linalg/networks-and-packing.md#two-map-networks) and
[Contraction trees](linalg/networks-and-packing.md#contraction-trees) give
the rules of occurrences, ports and plans with their codes.

> **Implementation note.** Execution is synchronous on one CPU. No
> asynchronous or device profile is implemented.
