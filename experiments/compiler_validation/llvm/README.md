# LLVM and foreign-runtime qualification

The [Lean-verified LLVM corpus](../../../llvm/docs/README.md) collects source-linked modules, their byte theorems and replay instructions.

This opt-in experiment measures the native-toolchain feasibility prerequisite
of [#749](https://github.com/MGYamada/Vastitas/issues/749) and
[#753](https://github.com/MGYamada/Vastitas/issues/753). It does not change the
compiler's production path. Its hand-authored LLVM fixture is not accepted
Vastitas Core, a modeled LLVM module, or a proof of either compiler.

The qualification executable and the compiler's optional `llvm-native` feature
share [the in-process adapter](../../../src/driver/llvm_backend.rs) and pin
`llvm-sys = "=231.0.1"`. The runner requires
LLVM **23.1.4**, Lean **4.35.0** at its release commit, and sequential locked
LP64 OpenBLAS **0.3.34**. A different LLVM patch version fails before Cargo
runs. The backend also checks the version of the library it actually links.
It uses the LLVM C API in process, without `llvm-as`, `opt` or `llc`.

## Run

Supply installed development prefixes explicitly. The script never downloads
or builds LLVM, Lean or OpenBLAS. Cargo runs offline by default; prepare the
locked dependencies separately, or opt in with `--allow-cargo-downloads`.
The LLVM prefix must already be usable, including any platform relocation
needed by a downloaded archive. A full source LLVM build is not required.

```sh
cargo fetch --locked --manifest-path experiments/compiler_validation/llvm/Cargo.toml
python3 experiments/compiler_validation/llvm/run.py \
  --llvm-prefix /path/to/llvm-23.1.4 \
  --lean-prefix /path/to/lean-4.35.0 \
  --openblas-prefix /path/to/openblas-0.3.34 \
  --output /path/to/empty-result-directory
```

The default `--link-mode static` requires LLVM's static libraries and their
system dependencies. `--link-mode dynamic` is an explicit separate experiment;
it does not satisfy the static-link qualification. `--target-dir` permits an
existing Cargo build cache. The result directory must be empty, so a rerun
does not overwrite retained evidence. No `CARGO_HOME`, `HOME` or other user
directory is repurposed.

To build the compiler with the native adapter and run its host-boundary
regressions against the same development prefix:

```sh
export LLVM_SYS_231_PREFIX=/path/to/llvm-23.1.4
cargo build --locked --offline --features llvm-native
cargo test --locked --offline --manifest-path experiments/compiler_validation/llvm/Cargo.toml --test handoff
```

The compiler feature requires static libraries. Both the source build and the
loaded library check the LLVM version. The default compiler build and ordinary
checks require no LLVM installation. The host tests link a fixture with the
system `cc`, run it, and exercise changed, truncated and extended handoffs,
an unexpected module target or layout, invalid SSA and an existing object.

The experiment loads the authorized fixture into memory. The adapter rereads
the handoff file, bounded by the expected length plus one byte, and compares
its complete contents with the expected bytes. LLVM's parser borrows this
same immutable buffer. A NUL sentinel outside the checked range supplies the
text parser's C boundary. The adapter verifies the parsed target and layout
against the selected target machine, runs LLVM's module verifier and emits an
object in memory before creating a new file. The target CPU is
`generic`, with no extra features. All operations in the fixture are calls,
integer status operations, branches and a phi; it has no FP instructions or
unproved alias/overflow flags.

The runner copies the repository's unmodified `IndexedRuntime.lean` into a
private build directory and compiles it with a small exported wrapper. A C
shim exports the Lean header's inline Nat operations with borrowed inputs
and owned results. Those objects form one foreign archive. The object from
LLVM links that archive, the pinned Lean runtime and the OpenBLAS archive.
The executable checks a Nat square beyond 64 bits, Euclidean Int division,
division by zero, Nat monus, an indexed-runtime operation and `s/d/c/zgemm`.
These are ABI/link/conformance checks, not floating error bounds or semantic
refinement proofs. The `s/c` probes call CBLAS directly; they do not establish
binary32 support in the production storage or numerical adapters.

The runner also checks that a changed byte, malformed LLVM and an incorrect
layout create no object. An existing object is never overwritten. Failures
write a `blocked` report and return a nonzero exit status; there is no
different-version or Lean/C fallback.

## Linux and macOS CI

The [native qualification workflow](../../../.github/workflows/llvm-linux.yml)
runs when a pull request changes the native adapter, its qualification suite
or the LLVM corpus. It also accepts a manual dispatch. The runner verifies
the SHA-256 of the upstream LLVM 23.1.4 SDK for Linux x86-64 or macOS arm64
before extracting the libraries and headers. Each job builds the static qualification
executable, runs the public native driver and compares the checked boxed
integer programs with Lean-generated controls. On Linux the foreign archive
links with the host C compiler selected through `leanc`, using the same libc
as the OpenBLAS build. The host linker uses the C++, C++ ABI, unwind, uv and
GMP archives supplied by the selected Lean release. The ABI report records
their names and hashes, along with the link driver. Each platform artifact contains the
ABI report, the exact LLVM input to the ABI experiment, any upstream
disassembly and the public conformance test summary.

On macOS the upstream SDK contains bitcode in its static libraries. Cargo
links these libraries with Xcode's Clang driver and the SDK's `ld64.lld`.
The workflow records the linker's version alongside the macOS ABI report.

## Measurements and comparison

`report.json` records input and tool/library hashes, target/layout, link mode,
artifact sizes, build-tree size, and separate wall time, CPU time and child
RSS for each phase. RSS means the maximum child-process high-water mark
reported by `getrusage`, **not** the sum of simultaneously resident processes.
A reused Cargo target directory yields a warm build measurement. Native run
time is one smoke invocation, not a Fast like C benchmark. The record omits
usernames, local prefixes and environment contents.

The comparison source is Lean's pinned `Lean/Compiler/IR/EmitLLVM.lean`. The
report records its hash and line locations for its ABI/untested notice,
fixed `size_t`, phi-generation TODO, inbounds GEPs and bitcode output.
`Comparison.lean` contains the matching integer/branch/pair examples. If the
Lean executable reports LLVM support, the runner attempts bitcode emission
and disassembly; a failed comparison is an explicit gap, never a correctness
verdict. If the binary lacks LLVM support, that fact is recorded directly.
The upstream emitter is a comparison target, not an oracle.

For the executable status fixture, Lean 4.35.0's `emitMainFn` generates an
`i64` entry with command-line and runtime initialization, IO error handling,
and reference-count cleanup. On a successful `IO UInt32` result it unboxes
the value and sign-extends it for return. The Vastitas preview's literal
`Int` entry obtains its status from the checked Euclidean remainder modulo
256. Its canonical `i32 @main()` returns that status directly and needs only
the platform startup objects. [Pinned Lean entry emitter](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L1488)

LLVM's native backend, LLVM's parser, the Lean compiler/runtime, the C shim
and OpenBLAS are foreign premises. A `passed` report establishes only this
host's fixture result. It does not qualify another operating system, produce
a self-contained release, authenticate public compiler evidence, or finish
#749/#753. Run on both Linux and macOS before making a cross-platform claim.

## Dependency-independent tests

```sh
python3 -m unittest discover -s experiments/compiler_validation/llvm -p test_run.py
cargo fmt --check --manifest-path experiments/compiler_validation/llvm/Cargo.toml
```

With the exact LLVM prefix available, also run Clippy and the qualification:

```sh
LLVM_SYS_231_PREFIX=/path/to/llvm-23.1.4 \
  cargo clippy --locked --manifest-path experiments/compiler_validation/llvm/Cargo.toml \
  --all-targets -- -D warnings
```

The experiment uses only the operating system SDK/compiler and explicit
prefixes; it loads no `.env` file. Results and caches belong outside the
source directory unless selected for reviewed retention in Git.

## Retained macOS result

[`results/macos-arm64/qualification.json`](results/macos-arm64/qualification.json)
records a passing arm64 macOS run, including all four CBLAS calls and the
three rejected inputs. [`program.ll`](results/macos-arm64/program.ll) is the
exact input recorded by that report. The Cargo build reused its target cache;
its timing is not a cold-build measurement. The upstream Lean binary reported
no LLVM feature, so executable EmitLLVM comparison remains a recorded gap.

LLVM came from the arm64 Golden Gate Homebrew bottle at formula revision
`424196fcd6ddcff867054edf33034db4d0c248c4`, with SHA-256
`4005890f2e921a5cacf6f3c0db9bdcfd73b44d8657660386811ae8e33639edfc`.
The bottle was extracted in a private temporary directory. Only its
`llvm-config` executable needed relocation of its z3/zstd library references
and a fresh ad-hoc signature; the installed LLVM was not changed. Static LLVM
linkage still left the backend dependent on host z3/zstd dynamic libraries.
Offline installation and the production source-to-LLVM proof chain have
separate acceptance requirements.

## Retained Linux result

The [Linux x86-64 qualification](results/linux-x86_64/qualification.json)
used static LLVM 23.1.4, the Lean 4.35.0 runtime and sequential LP64
OpenBLAS 0.3.34. All four CBLAS calls executed. The [2,691 input bytes](results/linux-x86_64/program.ll)
produced a 2,536-byte object. A one-byte change, malformed IR and a wrong
layout were rejected. The pinned Linux Lean executable reported no LLVM
feature for either upstream comparison fixture.

The [public integer controls](results/linux-x86_64/checked-integers.txt)
matched 121 native results across 15 checked libraries, all 15 heap ownership
probes and the three hosted executable statuses. The assembled entry returned
42 and rejected the sibling method; called and uncalled cross-package
methods returned 42 and 7. These were executions on a hosted Ubuntu system.
Offline distribution and broader source coverage are tracked separately.
[CI execution and handoff tests](https://github.com/MGYamada/Vastitas/actions/runs/44439825391/job/135277593119)

## Isolated lexical proof component

[`Bytes.lean`](../../../lean-kernel/VastitasKernel/LLVM/Bytes.lean) defines a
recursive decoder for canonical LLVM quoted bytes, using uppercase `\HH`
escapes. `parseQuotedComplete_iff` proves both directions: printing any byte
list decodes to that list, and every accepted input equals its complete
printed bytes. The bounded wrapper also proves its input length limit.

[`Syntax.lean`](../../../lean-kernel/VastitasKernel/LLVM/Syntax.lean) adds the
closed value-type spellings `i1/i8/i32/i64/ptr`, a separate `void` result type,
and canonical target/layout headers. `TargetHeader.parseBounded_iff` proves
the same complete-byte correspondence for accepted headers. Target fields
must be nonempty bounded ASCII atoms; those lexical conditions do not prove
that LLVM recognizes a target or that its layout matches a runtime ABI.

The 26 named theorems in
[`Regression.lean`](../../../lean-kernel/VastitasPublicTest/LLVM/Regression.lean)
check escapes, exact bounds, trailing bytes, unsupported type spellings and
target injection cases with official-kernel reduction. Run them with
`lake -d lean-kernel build VastitasPublicTest.LLVM.Regression`; the kernel regression
script includes that root. No public checker route imports these modules.
Typed instructions, CFG/phi validation, a whole-module parser, independent
LLVM semantics and MidIR refinement remain outside this lexical component.

## Static family call comparison

[FamilyComparison.vast](../../../tests/fixtures/FamilyComparison.vast) overloads `adjust` on `Nat` and `Int`. At input 2
the true branch calls saturating Nat subtraction and returns 0; the false
branch calls Int subtraction and returns −3. `tests/edition_families.rs`
checks both results in the native executable. `FamilyComparison.lean` is an
independently runnable translation with the two static targets made explicit.
`lean --run experiments/compiler_validation/llvm/FamilyComparison.lean` checks
the results; `lean -b` on the pinned macOS toolchain cannot emit bitcode
because `lean --features` reports `[]`. Thus no instruction count or binary
CFG comparison is available on that toolchain. In `EmitLLVM.lean` the fully
applied call uses the resolved declaration; Vastitas must settle the family
key and checked revision before constructing that call. Edit loans, returns
and the final seal are compile-time operations, not runtime calls.

The hand-authored `vq_family_evaluate` now makes the same two calls, with a
pointer phi at the join. Its ABI is `(i8, ptr, ptr) -> ptr`, matching the
generated C evaluator's byte-sized Bool and boxed Nat/Int arguments.
Subtraction borrows its input. The true branch transfers the owned Nat
result to `lean_nat_to_int`; the caller releases the returned Int on both
branches. This follows the pinned runtime header and generated C. In
`EmitLLVM.lean`, compare `emitFullApp` for a statically resolved call and
`emitJmp` for the join: the latter assigns to slots before branching, rather
than emitting this fixture's phi.

The qualification executable calls both the LLVM fixture and the generated
C evaluator on each branch for three input pairs, and checks each result
against an explicit decimal value. Inputs include 2, the subtraction
boundary 5, and boxed integers beyond 64 bits. The report records the
generated C digest and the native execution result even when the pinned
Lean binary cannot emit LLVM. None of these checks assigns a FunctionId or
authorizes a compiler-generated module.

Two more LLVM functions cover the mixed `Nat/Int` and `Int/Nat` division
keys. For each public signature the generated C and the hand-written LLVM
retain the borrowed Nat, convert it to an owned Int, pass the arguments to
Euclidean division in source order, and release the temporary. The test
checks both operand orders on small signed values, either zero denominator
and boxed integers larger than 64 bits.

## Unary finite-table module

The recorded macOS arm64 run produced a [604-byte LLVM module](results/macos-arm64/unary-table.ll) and [comparison report](results/macos-arm64/unary-table.json).
After building the public kernel, frontend, LLVM regression target and the
qualification backend, run the smaller native comparison separately.

```sh
python3 experiments/compiler_validation/llvm/run_table.py \
  --frontend target/debug/vastitas \
  --backend /path/to/target/debug/vastitas-llvm-qualification \
  --lean-prefix /path/to/lean-4.35.0 --llvm-prefix /path/to/llvm-23.1.4
```

`TableComparison.vast` defines a library with one public function, `pick`,
which performs a unary lookup. `TableMain.vast` imports it and checks all
three keys through the ordinary public native build. The experiment then
rechecks the library's exact function revision, lowers its complete checked
Core to optimization and execution MidIR, and requires a single function
whose sole instruction looks up its argument and returns that result. The
selected function, table and carriers retain their nominal owners in the
certificate. The adapter emits the switch under the fixed foreign signature
`i32 @vq_lookup(i32)`. The input carrier fixes the case order even when
source rows are permuted. Each result is an ordinal in the output carrier.

The independent theorem `VastitasOracle.UnaryFunction.correspondence` relates
evaluation of the returned Core function, both MidIR stages, the modeled
switch and its complete printed bytes for every in-range ordinal.
`foreign_miss` specifies the sentinel for every other foreign input. The
harness checks the linked object on every key and three out-of-range ordinals.
It also checks that a private function, a request for the wrong owner, a
constant function body and a second declared function all fail before byte
emission. A changed result digit fails the handoff comparison.

`TableBoundary.lean` also generates an empty module and a module containing
all 4,096 cases in reverse output order. Each round-trips through the complete
byte parser. The runner checks the linked executable and Lean evaluation
against the expected result for every ordinal from 0 through 4096 and for
UINT32_MAX. Ten altered modules exercise trailing bytes, default and case
edges, the sentinel, duplicate keys, the returned ordinal, the row count and
a complete 4,097-case CFG. The report records the canonical parser and byte
handoff results separately from raw libLLVM's handling of the same bytes.

Lean 4.35.0's `emitCase` zero-extends its tag to i64 before building a switch.
For exhaustive constructors without a default, `ensureHasDefault'` uses the
final constructor body for the default block. The foreign u32 table ABI here
assigns every invalid ordinal to its own block returning UINT32_MAX. The test
compares native results against both the Lean model and the explicit-domain
Lean case in `TableComparison.lean`. The report identifies whether upstream
bitcode could be emitted and disassembled. The measured native evidence covers this host and this
whole-library specialization. General function code generation, storage and
Fast/Official release modes remain open.

## Static call between two checked functions

`CallComparison.vast` exports `forward` and `pick`. The compiler records
the call from `forward` to `pick` with its Core symbol and specialization
key. The MidIR call operation carries the selected FunctionId, symbol,
specialization key, full parameter types and result type. The module checks
the acyclic call edges against the emitted call records with their exact
multiplicities. Both MidIR phases retain the shared checked revision.
The general MidIR theorem `VastitasOracle.MidIR.execute_invoke` proves equal
linked observations for every call depth, selected target and argument list.

The two-function LLVM specialization accepts a public unary forwarder and a
public unary table lookup with the same nominal signature. Both exports have
the foreign ABI `i32(i32)`. `vq_forward` passes its argument to `vq_lookup`
once and returns the resulting ordinal. `VastitasOracle.CallFunction.correspondence`
relates every in-range input in the exact checked caller Core, both linked
MidIR phases, the modeled LLVM function and the complete parsed bytes.
`foreign_miss` covers out-of-range ordinals at the modeled foreign boundary.

With the public kernel and frontend built against the same sources, run

```sh
python3 experiments/compiler_validation/llvm/run_call.py \
  --frontend target/debug/vastitas \
  --backend /path/to/target/debug/vastitas-llvm-qualification \
  --lean-prefix /path/to/lean-4.35.0 --llvm-prefix /path/to/llvm-23.1.4
```

The [macOS arm64 report](results/macos-arm64/static-call.json) records the
[709-byte module](results/macos-arm64/static-call.ll) produced by the pinned
toolchain. The native harness invokes each exported symbol on all three declared
inputs and three out-of-range inputs. It checks changed source owners,
argument, parameter type, visibility and bypass of the callee. Byte changes
cover call redirection, argument replacement, the return ABI, function
order and trailing bytes. The public compiler's native backend also runs
the checked source application. Lean 4.35.0's `emitFullApp` obtains the
selected declaration's function type and symbol, loads each argument slot,
issues `buildCall2` and stores the result. In the modeled module the entry
argument and call result are SSA values. The report identifies upstream
bitcode availability separately from matches with the running Lean reference.

## Public executable status preview

The public executable fixtures return −2¹²⁸−1 and the result of
`7 / (−3) + 12`. Both use the process exit status convention for unbounded
integers. The runner captures the function revision for the physical entry
file, verifies its protected operator identities and argument types, and
requires the same revision when running `check --llvm-preview`, the LLVM
build and the default Lean/C build. It compares the complete assembly with
the retained bytes for the corpus target. Supply the frontend built with
`--features llvm-native` and a qualification executable built against the
same pinned LLVM. [Literal source](../../../llvm/fixtures/ExitStatus.vast) ·
[Arithmetic source](../../../llvm/fixtures/FoldedArithmetic.vast)

```sh
python3 experiments/compiler_validation/llvm/run_exit.py \
  --case folded-arithmetic \
  --frontend target/debug/vastitas \
  --backend /path/to/target/debug/vastitas-llvm-qualification \
  --llvm-prefix /path/to/llvm-23.1.4 --lean-prefix /path/to/lean-4.35.0
```

Use `--case exit-status` for the signed literal. On macOS arm64 each case
matched all 374 bytes of its retained file and produced a 512-byte object.
The installed arithmetic program returned 10 and the literal program returned
255. The generated Lean/C executable, the separately linked object and a Lean
reference expression all agreed. Each report records the source, revision
and compiler fingerprints, target and ABI, linker and dynamic libraries.
The complete LLVM build timing includes checking, object generation, linking
and installation. Separate controls time the adapter and the linker. These
single runs include process startup and use the host's caches.
[Arithmetic report](results/macos-arm64/folded-arithmetic.json) ·
[Literal report](results/macos-arm64/exit-status.json)

In the pinned Lean 4.35.0 emitter, `emitNumLit` chooses the Lean Nat runtime
constructor for an object literal and an LLVM constant for a scalar.
`emitFullApp` resolves the function and constructs its typed call from the
Lean IR operands. Vastitas' arithmetic fixture folds the checked mixed
Nat/Int division and addition to a single LLVM return with value 10. The
pinned Lean binary reported no LLVM feature, so the upstream comparison
uses the implementation source. [emitNumLit](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L626) ·
[emitFullApp](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L755)

Use `--case assembled-bool` with the same command to run the manifest example.
The ordinary `choose` method returns false. The `winner` contribution supplies a
second method that returns its Bool argument. After `assemble choose { apply
winner; }`, calling `choose(true)` selects the second method and the true branch
returns 42. [Assembled Bool source](../../../llvm/fixtures/AssembledBool.vast)

The runner creates an edition-2026 package named `assembled_bool`, checks the
physical root bytes and their offset following the manifest, and inspects the
checked `choose` FunctionId, Bool key, contribution owner and method ordinal.
It matches the call to its Core symbol and checks all three specializations,
including the unselected method. Both builds and the preview check use the
complete captured revision. The retained revision digest includes the
temporary manifest's canonical path, so it can differ on a later run.

On macOS arm64 the preview matched all 688 retained bytes and emitted a
912-byte object. The installed executable, the separately linked object,
the default Lean/C build and the independent Lean reference each returned 42.
[Host qualification report](results/macos-arm64/assembled-bool.json)

Lean 4.35.0's `emitFullApp` builds a typed call, `emitCase` widens the tag and
emits a switch, and `emitJmp` stores join arguments before branching.
The Vastitas module calls the selected Bool method, branches on the i1
result and uses an i32 phi at the join. A separate Lean program calls a
`@[noinline]` Boolean identity function with `true` and returns the status
from the same conditional.
[emitFullApp](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L755) ·
[emitJmp](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L1050) ·
[emitCase](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L1104)

## Binary category composition and the closure unit

`run_binary.py` compiles the public S3 composition function and links a C
caller to its two-argument ordinal ABI. A separate Lean program applies the
two permutations to the three points and recovers the result ordinal. The
generated Lean/C client checks all 36 named results. The LLVM comparison
adds inputs outside each individual axis, including `UINT32_MAX`.
`run_table.py --case closure-unit` applies the unary qualification to the
selected unit of the closure Monad on the two-object chain. Both runners
accept `--frontend`, `--backend`, `--lean-prefix` and `--llvm-prefix`.
[Binary host run](results/macos-arm64/s3-composition.json) · [Unit host run](results/macos-arm64/closure-unit.json)

## Whole finite Kleisli executable

The closure package calls `unit`, `bind`, `compose` and `lift` through the
named Kleisli category and triple of a closure Monad on `lo < hi`. The
qualification replays the checked function revision for each build. The
original source and a variant that reverses one comparison exercise both
inputs of the final phi. A third source calls
`monad::kleisli::extend::<Triple, Obj::lo, Obj::hi>(C::up)` and returns
42 when the result is the identity at `hi` and the original checks pass.
[Closure package](../../../examples/packages/finite-kleisli/src/main.vast)

For each source, the package probe reads the exact input from the revision,
compares the root source bytes, checks protocol 10 again, and rebuilds the
finite program. It requires the full revision, parsed LLVM model and complete
assembly to match. The portable report lists local and original addresses,
callee edges and the selected Monad and object arguments. For the extension
it also records the actual execution MidIR operations and LLVM function
body. The unary lookup uses `M`'s `closeArr` table. The binary lookup
uses `C`'s `comp` with the multiplication component first and the mapped
arrow second.

```sh
python3 experiments/compiler_validation/llvm/run_kleisli.py \
  --frontend /path/to/llvm-native/vastitas \
  --backend /path/to/vastitas-llvm-qualification \
  --lean-prefix /path/to/lean-4.35.0 \
  --llvm-prefix /path/to/llvm-23.1.4
```

The runner compares the public native build, Lean/C build, and execution of
the parsed LLVM model. A separate llvm-sys control emits an object from the
exact public bytes and links it with the system C driver. The tests present
a truncated module, a duplicate phi predecessor, a reversed comparison, and
swapped branch destinations to the original byte handoff. The last two also
have separately parsed canonical models and independently linked control
executables with the changed status.

In the extension variant two direct LLVM calls pass the checked Hom
ordinals in SSA registers. Each table helper uses an `i32` switch. Lean
4.35.0's `emitFullApp` loads call operands from their slots, calls
`buildCall2` and stores the result. Its `emitCase` builds a switch on
a single constructor tag. For a join, `emitJmp` stores incoming values
before jumping. The Vastitas exit block uses explicit phi operands for
the two predecessors. The runner records these source lines and attempts
bitcode emission and disassembly when the pinned Lean binary exposes the
LLVM feature. [Independent closure and extension](KleisliComparison.lean) ·
[macOS arm64 result](results/macos-arm64/finite-kleisli.json)
