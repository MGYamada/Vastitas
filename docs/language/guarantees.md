# Guarantees

A **guarantee** is a property that every program that the compiler accepts
has, or that every run of the compiler has. The compiler **accepts** a
program when `vastitas check` reports no [diagnostic](diagnostics.md) for it.
`vastitas build` checks the same rules, needs an
[entry point](programs.md#the-entry-point) and then builds the executable. This chapter states the guarantees of the
language as rules. Each section then says what backs its rules, with the
status words Implemented, Tested, Proved and Planned of the
[Introduction](../index.md#what-exists-today), and links the chapter that
holds the evidence. A rule is a guarantee only as far as that evidence
reaches. [Verification boundaries](../verification.md) states what each
theorem assumes, and this chapter changes none of those statements.

Two groups of guarantees stay with their constructs.
[Selection](../stage1a.md#selection) says that every call of a generic has
one winner, and [Edit authority](edit-authority.md) says which
declarations may add a method to a generic.
[Verification boundaries](../verification.md) holds their evidence.

## What acceptance means

Acceptance is a statement about one program and one compiler: the checker
found no rule that the program breaks. Four statements about an accepted
program differ in what backs them, and the book keeps them apart.

| Statement | What it says | What backs it |
| --- | --- | --- |
| Checker acceptance | The program breaks no rule that the checker enforces | The checker: Implemented, and Tested by the regressions of each construct |
| Mathematical meaning | A construct denotes the mathematical object that its chapter describes | Proved for the properties that a theorem states, under its premises. [Verification boundaries](../verification.md) states the theorems, and the [specifications](../specifications.md) record some of them as Proved claims. Nothing else is claimed |
| Floating-point behaviour | The values that an executable computes in binary64 arithmetic | Not guaranteed, apart from the rules of [Floating-point values](#floating-point-values) |
| Native refinement | The executable computes what the checked program denotes | Not Proved. Tested by the executables that the tests build and run |

**Native refinement** is the statement of the last row: the executable that
the native build produces computes the value of the program that the checker
accepted.

The [checker](../appendix/glossary.md#checker) is the part of the compiler
that decides whether a program breaks a rule.

Rules:

- The compiler enforces the rules of the Reference that give a code, as
  [Rules](notation.md#rules) defines. A program that breaks such a rule is
  not accepted, unless the rule says that the executable checks it at run
  time.
- Acceptance does not say that a program computes what its author intends.
- Acceptance says that a mathematical property holds only where a theorem
  states the property, under the premises of the theorem. The
  specifications record some of these properties as Proved claims.
  [Metric evidence](../spec/metric-evidence.md) is an example.
- The language formalizes no general theory of schemes or of smooth
  manifolds. Acceptance certifies no numerical accuracy and no physical
  adequacy.
- A theorem about an accepted program is a theorem about the program that
  the checker reads, or about the program that the checker builds from it.

The evidence: the enforcement of the rules is Implemented, and Tested for
the rules that the regressions exercise. That the program which the checker
reads is the program that the source denotes is Tested, not Proved. The
[assumption registry](../spec/assumptions.md) lists the trusted components,
and
[What is outside these claims](../verification.md#what-is-outside-these-claims)
gives the boundary of the theorems.

> **Implementation note.** The compiler has two parts. The
> [frontend](../appendix/glossary.md#frontend) reads the source files and
> sends the program to the [kernel](../appendix/glossary.md#kernel) as a
> request of the [wire protocol](../appendix/glossary.md#wire-protocol). The
> kernel is the checker, and it generates the code. The frontend enforces
> the rules on source text, files and manifests. The kernel enforces every
> rule on names, types, dispatch, authority and resources, including a rule
> that the frontend reports first.

## Check before generating

Rules:

- `vastitas build` generates an executable only from a program that the
  checker accepts. No command accepts a program on the result of the frontend
  alone.
- The checker checks the whole program before the compiler generates code. It
  checks every function, method and lambda, and every resource function, even
  one that no call reaches. [The entry point](programs.md#the-entry-point),
  [Selection](../stage1a.md#selection),
  [Specialization](../stage1b.md#specialization) and
  [Resource functions](../storage/resource-programs.md#resource-functions)
  give these rules.
- The checker resolves every name, assigns every identity and checks every
  body itself. It takes no name, identity or annotation on trust.
- The compiler generates code from the program that the checker checked, and
  from no other.
- A `build` that fails leaves an existing output file as it was. Compilation
  never runs the generated program.

The evidence: Implemented, and Tested by the tests of the driver and of the
kernel. Proved: a code generator of the kernel returns code only when the
check that it repeats on its input succeeds.
[Current public checker routes](../verification.md#current-public-checker-routes)
names the entry points, and
[What is outside these claims](../verification.md#what-is-outside-these-claims)
the theorems on generation. [Appendix A](../guide/cli.md) describes the
commands.

> **Implementation note.** The kernel trusts no name, identity or annotation
> of the request that the frontend sends. Before it returns code, the
> generator of pure code checks the types of the
> [Core](../appendix/glossary.md#core) module again, and the generator of
> storage code audits the schedule again. For wire protocols 8 and 9 an
> oracle theorem states that the generator receives the result of the check
> of the same request. For protocols 2 to 7 the entry point of the kernel passes the
> result of the check to the generator, and the oracle does not import that
> entry point.

## Termination

Rules:

- The evaluation of every function of an accepted program ends, for every
  argument. The language has no loops, and a cycle of calls is an error.
  [Calls](functions.md#calls),
  [Selection](../stage1a.md#selection) and
  [Specialization](../stage1b.md#specialization) give this rule for
  functions, for generics and for function values.
- Dispatch is finite. A generic has finitely many keys, and the compiler
  selects the method of every call when it checks the program, as
  [Selection](../stage1a.md#selection) says. An executable selects no method.
- A call of a function value has one target that the compiler knows, as
  [Static targets](../stage1b.md#static-targets) says.
- A resource function has no loops. An executable runs its statements in
  order, each at most once for each call of the function. A cycle of calls
  of resource functions is an error, as
  [Resource functions](../storage/resource-programs.md#resource-functions)
  says.
- Termination is no bound on the time, the memory or the stack of a run.

The evidence: Implemented and Tested. Proved for pure functions: every
function of the Core that the checker returns evaluates in finitely many
steps to a value of its result type. In a program that `vastitas build`
accepts, a `main` that is not a resource function evaluates to an integer.
[Indexed term, function and checked-program evaluation](../verification.md#indexed-term-function-and-checked-program-evaluation)
and [Code generation entries](../verification.md#code-generation-entries)
state the theorems. They are about the kernel's evaluator of
[Core](../appendix/glossary.md#core), not about native code. No theorem
states that the statements of a resource function end, and a native routine
such as a matrix product is outside every theorem.

## Exact integers

Rules:

- `Nat` and `Int` have no bound, as [Scalar types](types.md#scalar-types)
  says. The operations of
  [Operator expressions](expressions.md#operator-expressions) on them are
  exact: no operation overflows, wraps or rounds.
- The difference of two `Nat` values is 0 where it would be negative. No
  value of type `Nat` is negative.
- A value of type `Nat` becomes a value of type `Int` only through `int`, and
  no function converts back.
- An implementation that changes these integers into machine integers does
  not meet the performance goal, as
  [Fast like C](../storage-ownership.md#fast-like-c) says.

This program subtracts 5 from the `Nat` value 2 and compares the result with
0. Its executable prints `-42`:

```vast
{{#include ../../examples/book/expressions/saturating-subtraction.vast}}
```

The evidence: Implemented, and Tested by programs that the tests build and
run. The theorems on evaluation speak of the unbounded integers of Lean.
That an executable computes them rests on the Lean runtime and its
large-number library, which the
[assumption registry](../spec/assumptions.md#assumption.lean-rat-gmp) lists.
[std::arithmetic::generic](../spec/std-arithmetic-generic.md) records what is
Proved about the promotion of `Nat` and `Int` in the standard library.

## Nothing implicit

Rules:

- No value converts implicitly between `Nat` and `Int`, as
  [Operator expressions](expressions.md#operator-expressions) says, or between
  the two settings of geometry, as
  [Settings and markers](geometric-types.md#settings-and-markers) says.
- Only `allocate` and `runtime_allocate` allocate cells. A statement copies
  cells only where its rules say so.
  [Resource statements](../storage/resource-programs.md#resource-statements)
  and the numerical chapters give the statements that copy.
- No statement conjugates unless the program writes a conjugation, as
  [Transforms, evaluation and metrics](../linalg/transforms-and-metrics.md)
  says. A matrix product conjugates nothing and transposes nothing, as
  [Matrix products](../linalg/maps-and-gemm.md#matrix-products) says.
- No operation selects a metric by default, not even the Euclidean metric. A
  metric enters only where the program names one, as
  [Metrics](smooth-declarations.md#metrics) and
  [Metrics of numerical maps](../linalg/transforms-and-metrics.md#metrics)
  say.
- No operation selects a frame by default, not even the coordinate frame. A
  frame primitive applies only the frames that its declaration names, and no
  frame primitive reads a metric: the Gram matrix of a metric in a frame is a
  composite of `flat` with encoding and decoding, as
  [The frame profile](frames.md#the-frame-profile) and
  [The Gram matrix in a frame](frames.md#the-gram-matrix-in-a-frame) say.
- A declaration of a physical dimension changes no declaration of another
  kind, apart from the limits of a whole program and name clashes. A
  metric is valid, and `flat` and `sharp` compute the same values, with and
  without readings, scales and physical interpretations of it, and a program
  without them has the same generated code, as
  [Scope of physical dimensions](physical-dimensions.md#scope-of-physical-dimensions)
  says.
- The rule on allocation concerns the cells of allocations. It says nothing
  about the memory that an executable uses for integers and other pure
  values.

`Nat` and `Int` operands do not mix:

```vast
{{#include ../../examples/reject/expressions/mixed-integers.vast}}
```

```text
{{#include ../../examples/reject/expressions/mixed-integers.stderr}}
```

The evidence: Implemented and Tested. The rules on copies and allocations
are rules of [Storage and ownership](../storage-ownership.md) on the
compiler, and that chapter says that such a rule is not evidence. Proved:
the request that the checker schedules for a network or for an evaluation has
the conjugation flags of its operands. Also Proved, for smooth declarations:
a declaration of a metric changes neither the validity nor the value of a
primitive other than `flat` and `sharp`. Also Proved, for frames and
physical dimensions: no frame primitive reads a metric declaration, a frame
declaration changes neither the validity of another declaration nor the
validity of a primitive that names none of its frames, and a declaration of
a physical dimension changes neither the validity of a declaration of another
kind nor the validity or the value of any primitive. The two statements on
the validity of declarations hold for every table of class ranks. That the
table of class ranks stays the same is not proved, so they are not stated
for the validity of a whole program. That the generated code stays the
same is Tested. [What is outside these claims](../verification.md#what-is-outside-these-claims),
[Smooth affine geometry and reverse pullbacks](../verification.md#smooth-affine-geometry-and-reverse-pullbacks)
and [Frames and physical dimensions](../verification.md#frames-and-physical-dimensions)
state these theorems. They are facts about the checked program, not laws of
the arithmetic that a native routine performs.

## Nominal identity

Rules:

- Objects, spaces, bases and allocations have
  [nominal identity](../appendix/glossary.md#nominal-identity). Each comes
  from one construction or declaration, as
  [Object identity](geometric-types.md#object-identity),
  [Spaces and bases](../linalg/maps-and-gemm.md#spaces-and-bases) and
  [Identities and rights](../storage-ownership.md#identities-and-rights) say.
- Equal dimensions, shapes, layouts or names never make two of them the
  same. An accepted program uses a value of one identity only where its
  rules ask for that identity.
- An extent that a program computes proves no identity, as
  [Runtime extents](../storage/resource-programs.md#runtime-extents) says.
- Frames and quantity kinds are nominal too. Two frames are different frames
  even when their columns are equal, so their arrays have different types, as
  [The frame profile](frames.md#the-frame-profile) says. Two quantity kinds
  are different kinds even when their dimensions are equal, as
  [Base dimensions and quantity kinds](physical-dimensions.md#base-dimensions-and-quantity-kinds)
  says.
- Identity is a property of the checked program. An executable holds no
  identities, and two objects of one setting and one dimension have equal
  descriptors when the program runs.

In this program `X` and `Y` have the same dimension, and `p` is a point of
`X` only:

```vast
{{#include ../../examples/reject/geometric-types/wrong-endpoint.vast}}
```

```text
{{#include ../../examples/reject/geometric-types/wrong-endpoint.stderr}}
```

The evidence: Implemented and Tested. Proved: the evaluation of the Core
that the checker returns preserves its typing, in which a point and a
morphism keep both endpoints. The checked numerical operations keep the
objects and the bases of their maps. An accepted call of a frame primitive
has its operands in the frames that its declaration or its other operands
name, and `normalized` accepts only a scale of the kind of its coordinate.
[Verification boundaries](../verification.md#indexed-term-function-and-checked-program-evaluation)
and [Code generation entries](../verification.md#code-generation-entries)
state the first,
[What is outside these claims](../verification.md#what-is-outside-these-claims)
the second, and
[Frames and physical dimensions](../verification.md#frames-and-physical-dimensions)
the last two.

## Storage

In an accepted program, the rules of
[Resource programs](../storage/resource-programs.md) hold on every path
through every resource function.

Rules:

- A statement reads a cell only after a statement on every path to it wrote
  the cell.
- Two live loans whose views may overlap are both `read` loans. A loan and
  its children are the exception: while a child is live, its parent gives no
  access.
- No loan outlives the function that borrowed it, and no loan leaves a
  function through a result. The checker rejects every escaping loan, as
  [Ownership and explicit transitions](../storage-ownership.md#ownership-and-explicit-transitions)
  says.
- A program frees every allocation once. At the end of a function, the body
  has dropped each owner, moved it, handed it to a call or returned it as an
  owned result.
- [Resource statements](../storage/resource-programs.md#resource-statements)
  gives the error of a program that breaks one of these rules.
- The checker treats views that may overlap as overlapping, and it rejects
  some programs whose accesses are disjoint.
  [Resource statements](../storage/resource-programs.md#resource-statements)
  says which.

This program writes one column of a view and then reads both:

```vast
{{#include ../../examples/reject/packages/uninitialized-read/main.vast}}
```

```text
{{#include ../../examples/reject/packages/uninitialized-read.stderr}}
```

The evidence: Implemented and Tested. Four facts are Proved for the model of
storage that the checker keeps. The bytes of every accepted access lie in its
allocation. An accepted read finds initialized bytes. Two active loans of
which one writes do not overlap; a loan with a live child is not active and
gives no access. At the end of an accepted entry point the model
holds no allocation and no loan.
[What is outside these claims](../verification.md#what-is-outside-these-claims)
states the theorems, and
[Resource checking](../internals/resource-checking.md#independent-checking-and-proof-boundary)
the boundary. Not Proved: that the memory of an executable agrees with this
model. The proofs trust the native runtime, its allocator and the C compiler,
and tests exercise them.

## Run-time checks

A **run-time check** is a check that an executable makes on values that the
compiler does not know, and whose failure stops the executable.

Rules:

- An executable checks each `expect` and `runtime_expect` statement, and each
  condition on [runtime extents](../storage/resource-programs.md#runtime-extents)
  that the compiler cannot decide.
- An executable checks the conditions of a storage or numerical operation
  before the first write of that operation. The conditions concern its
  allocations, views and sizes.
  [Matrix products](../linalg/maps-and-gemm.md#matrix-products) says so for
  `gemm`.
- A run-time check that fails stops the executable with a
  [run-time diagnostic](diagnostics.md#run-time-diagnostics). The executable
  prints no result and exits with an unsuccessful status.
- Writes that the executable completed before it stopped are not undone. It
  frees its allocations, as
  [Running a resource program](../storage/resource-programs.md#running-a-resource-program)
  says.

The evidence: Implemented, and Tested by executables whose checks fail.
[Resource checking](../internals/resource-checking.md#runtime-extent-proof-boundary)
states what is Proved about the conditions on runtime extents, including the
agreement of the runtime's Lean helpers with the checker on the layout
conditions. No theorem covers the C code of the runtime.

## Determinism

Rules:

- The result of a check depends on the command, on the files that it reads
  and on the compiler. Two runs of one command on the same files accept the
  program or reject it alike, and they report the same diagnostics.
- No check has a time limit. Every [limit](limits.md) counts units of work
  or of size, so the speed of a machine does not decide acceptance.
- A run that fails for lack of memory, or that a signal interrupts, accepts
  nothing.
- The order of method declarations never decides which method a call
  selects, as [Selection](../stage1a.md#selection) says.
- Every `build` of one accepted program by one compiler generates the same
  program text.

The evidence: Implemented, and Tested on macOS and on Linux by tests that
compare diagnostics and generated programs with recorded text. Proved: the
selection of methods does not depend on the order of the method records, as
[Verification boundaries](../verification.md#stage-1a-finite-dispatch-and-checker-composition)
states. No theorem states the determinism of the whole compiler, and these
rules do not cover the native build of an executable.
[Verification boundaries](../verification.md) describes the audit of the
compiled code of the checker.

## Floating-point values

Rules:

- A payload is a binary64 value, exactly. The compiler never rounds a
  payload, and `store` and `fill` write its bits, as
  [Payloads](../storage/resource-programs.md#payloads) says.
- `expect` compares the bits of a cell with the bits of a payload.
- A matrix product computes in binary64 arithmetic, in the order of
  operations of the native routine. Its result is not an exact product of
  real numbers, as
  [Matrix products](../linalg/maps-and-gemm.md#matrix-products) says.
- Acceptance certifies no identity of real numbers and no equality of bits
  between platforms for a computed cell, as
  [The GEMM contract](../storage-ownership.md#the-gemm-contract) says.

The evidence: the rules on payloads are Implemented and Tested. No theorem
states a property of a floating-point result.

## What is not guaranteed

An accepted program cannot rely on the following.

- The results of floating-point operations, beyond the rules of
  [Floating-point values](#floating-point-values).
- The behaviour of native libraries such as BLAS. A numerical executable
  calls the pinned library that [Appendix A](../guide/cli.md#numerical-builds)
  names, and no check or theorem covers what that library computes.
- Native refinement: that the Lean compiler and the C compiler translate the
  generated program into an executable that computes it. The
  [assumption registry](../spec/assumptions.md#assumption.lean-to-c) lists
  this assumption.
- That the frontend writes the request that the source denotes. This is
  Tested, as [What acceptance means](#what-acceptance-means) says.
- The time, the memory and the stack of a check or of a run.
  [Limits](limits.md#what-has-no-limit) says what the limits do not bound.
- Performance. Fast like C is an aim of the design, and
  [Storage and ownership](../storage-ownership.md#fast-like-c) states it as a
  C/C++-class target. It does not assert that programs reach that
  performance.
  [Performance evidence and acceptance](../storage-ownership.md#performance-evidence-and-acceptance)
  holds the conditions of its acceptance and their status.
- The text of a diagnostic, as [Codes](diagnostics.md#codes) says.
- Anything that the book marks Planned. A Planned feature is not available,
  and a Planned claim of a specification has no evidence.
