# Compiler architecture

This chapter names the components of the compiler. It says what each
component receives and produces, what the compiler relies on each component
for, and which path a program takes from its source files to an executable.
Each step of that path links the chapter that describes it. The rules of the
language are in the Vastitas Reference.
[Guarantees](../language/guarantees.md) states what acceptance means, and
[Verification boundaries](../verification.md) states what is proved.

## Components

The [frontend](../appendix/glossary.md#frontend) is the Rust crate `vastitas`
in `src/`. Its parser and its resolver turn source text into the declarations
of a request of the [wire protocol](../appendix/glossary.md#wire-protocol).
The **driver** is the rest of the frontend. It reads the command line and the
input files, starts the kernel, shows the diagnostics, runs the native build
and writes the output file. The [kernel](../appendix/glossary.md#kernel) is a
separate Lean program, `vastitas-kernel`. A **code generator** is a function
of the kernel that writes Lean source for a checked program. A **native
runtime** is a library that a generated program links. An **arena** is an
object of the storage runtime that holds buffers of a generated program. The
generated `main` creates an arena at its start, when an operation of the
checked entry needs one, and closes it at its end.

| Component | Directory | Receives | Produces |
| --- | --- | --- | --- |
| Parser and resolver of the frontend | `src/frontend.rs`, `src/frontend/`, `src/ir.rs`, `src/indexed.rs`, `src/storage.rs` | The text of each source file | The declarations of a request, with unresolved names and source positions |
| Driver of the frontend | `src/driver.rs`, `src/sources.rs`, `src/packages.rs`, `src/process.rs`, `src/runtime_inputs.rs`, `build.rs` | The command line, the manifests and the source files | The request, the diagnostic lines, a Lake project for the native build and the output file |
| Kernel | `lean-kernel/Main.lean`, `lean-kernel/VastitasKernel/` | One request on standard input and the mode `check` or `emit` | One response on standard output: acceptance or one diagnostic |
| Code generators | `IndexedCodegen.lean`, `ResourceCodegen.lean`, `StorageCodegen.lean` and `StorageShapeCodegen.lean` in the kernel | The checked [Core](../appendix/glossary.md#core) and, for a resource entry, the checked resource schedule | The Lean source of the program, in the `emit` response |
| Kernel runtime | `IndexedRuntime.lean`, `AlgebraRuntime.lean` and `SmoothRuntime.lean` in the kernel | Calls of a generated program | The values of descriptor objects, points and morphisms, of exact polynomial algebra and of smooth maps |
| [Storage runtime](../appendix/glossary.md#storage-runtime) | `lean-kernel/native/` | Calls of a generated resource program | Buffers in an arena, with checks before each access |
| [Numerical runtime](../appendix/glossary.md#numerical-runtime) | `lean-kernel/numerical/` | Calls of a generated numerical program | Matrix products through OpenBLAS |
| Proof oracle | `lean/` | The definitions of the kernel | Theorems about those definitions. It has no executable |
| Mathematical bridge | `lean-bridge/` | The definitions of the kernel and of the oracle, and mathlib | Theorems that relate those definitions to mathlib's mathematics |
| Standard library | `stdlib/` | — | A package of `.vast` sources. The compiler gives it no privilege |

The kernel never reads a source file or a manifest. The frontend never
accepts a program. The [oracle](../appendix/glossary.md#oracle) and the
[mathematical bridge](../appendix/glossary.md#mathematical-bridge) never run
during a compilation or in a generated program.

## From source files to an executable

1. **Command line.** `vastitas check` or `vastitas build` names an entry file
   with its libraries, or a manifest. For `build` the driver checks the output
   path before it reads an input.
   [The command line](../internals/driver.md#the-command-line).
2. **Reading.** In [flat mode](../appendix/glossary.md#flat-mode) the driver
   reads the entry file and the libraries, and then parses them. In
   [manifest mode](../appendix/glossary.md#manifest-mode) it reads and parses
   one file at a time: a manifest, the packages that it depends on, and then
   each module file of the package. It bounds the number and the size of the
   inputs. [Reading inputs](../internals/driver.md#reading-inputs) and
   [Loading packages](../internals/driver.md#loading-packages).
3. **Parsing.** The parser reads each file by itself. In flat mode the
   resolver then checks the names of the whole program. In manifest mode
   the parser leaves every path unresolved.
   [Parsing](../internals/driver.md#parsing).
4. **Request.** The driver chooses the version of the wire protocol and
   serializes one JSON request. The version follows from the declarations of
   the program and, in manifest mode, from the `geometry_compat` export of a
   manifest. [Protocol selection](../protocol.md#protocol-selection).
5. **Checking.** The driver starts the kernel with the mode `check` or
   `emit` and writes the request to its standard input. The kernel scans the
   text, decodes it by its version and checks the whole program.
   [Wire protocols 2–9](../protocol.md) describes the decoders. The checks are
   in these chapters:
   - names, modules and packages:
     [Protocol 3](../protocol.md#protocol-3-package-namespaces);
   - generics, dispatch and function values:
     [Checking pipeline](../internals/checking-pipeline.md);
   - indexed declarations, edit authority over them and the Core:
     [The indexed checker](../internals/indexed-checker.md);
   - resource functions: [Resource checking](../internals/resource-checking.md)
     and [Checked storage and resource calls](../storage/checked-storage.md);
   - numerical statements: [Numerical backend](../internals/numerical-backend.md).
6. **Generation.** In the mode `emit` the kernel passes the result of the
   check to a code generator. The generator checks its input again and
   returns Lean source.
   [Audited Core and native generation](../internals/indexed-checker.md#audited-core-and-native-generation),
   [All-body checking and generation](../internals/resource-checking.md#all-body-checking-and-generation)
   and
   [Native lowering and execution](../storage/checked-storage.md#storage-ir--native-lowering-and-execution).
7. **Response.** The driver reads one response. It compares the
   [build identity](../appendix/glossary.md#build-identity) of the kernel
   with its own. It shows the diagnostic of a rejected program at its place
   in the source files.
   [Starting the kernel](../internals/driver.md#starting-the-kernel) and
   [Rendering diagnostics](../internals/driver.md#rendering-diagnostics).
8. **Native build.** For `build` the driver compares the runtime files of the
   [kernel root](../appendix/glossary.md#kernel-root) with the files of its
   own build. It writes a Lake project that
   holds the generated source and runs Lake. Lean compiles the source to C,
   and the C compiler links it with the kernel runtime and with the storage
   and numerical runtimes that the response selects.
   [The native build](../internals/driver.md#the-native-build).
9. **Output.** The driver copies the executable to a
   [staging file](../appendix/glossary.md#staging-file) beside the output
   path and renames it onto that path.
   [Output files](../internals/driver.md#output-files).

`check` ends after step 7. The executable of step 9 prints the integer that
`main` returns, as [The entry point](../language/programs.md#the-entry-point)
says.

## The three checker routes

`lean-kernel/Main.lean` selects the checker by the version of the request.
[Current public checker routes](../verification.md#current-public-checker-routes)
states the theorems on these entry points.

| Wire protocol | Check | Generation in the mode `emit` |
| --- | --- | --- |
| 2 to 6 | `Indexed.LegacySource.check` decodes the request, adapts it to the indexed source checker and runs `Indexed.AuthoritySource.checkProgram` | `Main` passes the Core `compiled` of the check result to `Indexed.Core.Codegen.generate` |
| 7 | `Indexed.Wire.check` decodes the request and runs the same `Indexed.AuthoritySource.checkProgram` | The same call of `Indexed.Core.Codegen.generate` |
| 8 and 9 | `ResourceSource.Wire.check` runs the same checks on the pure bodies and the resource checks on the resource functions | `ResourceSource.Wire.emit` runs that check and passes its result to `ResourceSource.Codegen.generateChecked` |

`Indexed.Core.Codegen.generate` calls `generateLibrary` with `main` as the
root. `generateLibrary` checks the types and the dependencies of the Core
module again before it writes a function. `generateChecked` calls `generate`
for a program whose entry point is an ordinary function. For a resource
entry it calls `generateLibrary` with the Core functions of the value
fragments of the schedule as roots. It also compiles the checked schedule to
a native plan and compares the instructions that it emits with that plan. [Check before generating](../language/guarantees.md#check-before-generating)
states the guarantee and its evidence.

## What the compiler relies on each component for

| Component | The compiler relies on it for | Evidence |
| --- | --- | --- |
| Parser and resolver | The request is the program that the source files denote | Tested. Not Proved: the [assumption registry](../spec/assumptions.md) lists the frontend |
| Driver | It reads the files that the command names, runs a kernel of its own build, builds the source that the kernel returns and replaces only the output file | Tested by the tests that [The driver](../internals/driver.md) names |
| Kernel | Acceptance: every rule on names, types, dispatch, authority and resources | Implemented and Tested. Proved for the properties that [Verification boundaries](../verification.md) states |
| Code generators | The generated source is the program that the kernel checked | The repeated check is Proved to precede every returned source. That the source computes what the Core denotes is Tested, not Proved |
| Kernel runtime | The values of the operations that generated programs call: Lean definitions of the kernel | Proved for the properties that Verification boundaries states: [Primitive and package semantics](../verification.md#primitive-and-package-semantics), [Exact affine algebra checker](../verification.md#exact-affine-algebra-checker) and the [oracle theorems](../verification.md#oracle-theorems) of the smooth runtime. Tested otherwise |
| Storage and numerical runtimes | The effects of the storage and numerical operations that generated programs call: C code | Tested, in part under sanitizers. Not Proved |
| Lean toolchain, Lake and the C compiler | The kernel executable runs the definitions of the kernel, and a generated program runs its source | Trusted. [Native refinement](../appendix/glossary.md#native-refinement) is not Proved |
| Arithmetic of the Lean runtime | The rational and integer operations of the kernel runtime: Lean core `Rat` and the GMP library | Trusted |
| OpenBLAS | The matrix products of a numerical program | Trusted. Tested by the checks of the [native GEMM adapter](../internals/numerical-backend.md#native-gemm-adapter) |
| Proof oracle | Nothing during a compilation. Its theorems say what acceptance implies | Lean's type checker checks each proof. An audit admits the axioms `propext`, `Classical.choice` and `Quot.sound` only |
| Mathematical bridge | Nothing during a compilation. Its theorems give mathematical meaning to kernel definitions | Lean's type checker, an audit of its own with the same three axioms, and mathlib at a pinned commit |

A fault of the frontend can change which program the kernel checks. It cannot
make the kernel accept a request that breaks a rule. The third rule of
[Check before generating](../language/guarantees.md#check-before-generating)
states why.
[What is outside these claims](../verification.md#what-is-outside-these-claims)
lists what no theorem covers.

The [assumption registry](../spec/assumptions.md) has five entries. Four have
a row above: the parsing of the frontend, the Lean-to-C toolchain with the C
compiler, Lean core `Rat` with GMP, and mathlib, in the row of the bridge.
The fifth is the reflection of the promotion fixture, which
[Promotion proofs and fixture](../internals/checking-pipeline.md#promotion-proofs-and-fixture)
describes. The registry has no entry for the driver, for the C code of the
two runtimes or for OpenBLAS.

## Dependencies

| Package | Depends on |
| --- | --- |
| Rust crate `vastitas` | The crates of `Cargo.lock`. `build.rs` reads `lean-kernel/compiler-limits.json`, `lean-kernel/lean-toolchain`, the sources of the kernel executable and the runtime inputs of the kernel package, of `native/` and of `numerical/` |
| Lake package `vastitas_kernel`, `lean-kernel/` | The Lean distribution only |
| Lake package `vastitas_storage_native`, `lean-kernel/native/` | The Lean distribution and a C compiler |
| Lake package `vastitas_gemm_native`, `lean-kernel/numerical/` | `vastitas_storage_native` and an OpenBLAS prefix that the build names |
| Lake package `vastitas_oracle`, `lean/` | `vastitas_kernel` only |
| Lake package `vastitas_bridge`, `lean-bridge/` | mathlib at a pinned commit, `vastitas_kernel` and `vastitas_oracle` |

- Every Lake package pins the same Lean toolchain in its `lean-toolchain`
  file, and each keeps its `lake-manifest.json`.
- The kernel and the oracle import neither mathlib nor the bridge. The
  dependency of the bridge on them is one way.
  [ADR 0001, section 9](../adr/0001-mathematics-first-stdlib.md#9-mathematical-alignment-and-oracle-dependency-independence)
  holds this policy, with an amendment on the bridge.
- The storage runtime and the numerical runtime are packages of their own.
  Neither the kernel package nor the oracle depends on them.
- No compilation needs mathlib, and `check` needs no OpenBLAS. A build
  links the storage runtime when the checked entry uses an arena. It links
  the numerical runtime and OpenBLAS when the entry point reaches a
  [product statement](../appendix/glossary.md#product-statement): the
  native plan of the entry then holds a `gemm` or a `diagonalPair`
  instruction, or its runtime-shape events hold a GEMM.
- `build.rs` generates nine constants of the frontend from keys of
  `lean-kernel/compiler-limits.json`: `parseNesting`, `astDepth`,
  `moduleNesting`, `packageNesting`, `requestBytes`, `algebraNesting`,
  `algebraCoefficientDigits`, `algebraGenerators` and `assemblyEvents`. The
  kernel reads the same file when it is elaborated. Four bounds on the forms
  of resource functions are constants of `src/frontend/resource_parser.rs`.
  They repeat literals of the kernel's decoder and checker.

`scripts/check_boundaries.py` checks these dependencies: the toolchains, the
Lake configurations and manifests, and the imports of every Lean source of
the kernel, of the two runtimes, of the oracle and of the bridge. It also
checks that a runtime module imports no other module of the compiler. [Independent mathematical bridge](../verification.md#independent-mathematical-bridge)
describes the check of the bridge.

## Evidence

Implemented: every component of this chapter. Tested:

- `tests/compiler.rs::backend_is_required_and_failure_has_no_frontend_fallback`
  runs `check` with a kernel executable that does not exist and requires
  `E_BACKEND`.
- `tests/driver_hardening.rs::kernel_build_identity_fails_closed` gives the
  driver responses without a build identity, with another digest and with
  another Lean version. It requires an error for an accepted program and a
  note on the diagnostic of a rejected one.
- `tests/protocol_shape.rs` adds an unknown field to each record shape of a
  request and requires `E_PROTOCOL` from the kernel.
- `tests/emit_golden.rs::generated_lean_matches_the_emit_fixtures` compares
  the generated source of a corpus of programs with recorded files.
- `tests/examples.rs` builds and runs the programs of the book.
- `python3 scripts/check_boundaries.py` runs in CI before and after the Lean
  builds.

[Run compiler, proof and native checks](validation.md) lists the commands for
each component.

## History

The page was a table of directories with a summary of the proof boundary.
That summary is in [Verification boundaries](../verification.md), and the
description of the geometry library is in
[The indexed checker](../internals/indexed-checker.md#geometry-standard-library-declarations).
The temporary `stdlib/indexed` entry point of the geometry library has been
removed, and `stdlib` exports geometry and arithmetic together. General
mathematics of schemes and manifolds is Planned under
[#211](https://github.com/MGYamada/Vastitas/issues/211).
