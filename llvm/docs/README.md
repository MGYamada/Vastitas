# Lean-verified LLVM IR corpus

The corpus contains 38 complete LLVM assembly files from edition 2026 Vastitas source. Lean proves parser acceptance for eight files and equality with a canonical model printout for the other 30. Replay parses each of those 30 files and evaluates its executable models. The structured lookup and direct Kleisli operand each have macOS arm64 and x86-64 Linux files. The other samples target macOS arm64. [Files](../src/) · [Concrete proofs](../Corpus.lean)

## Modules

| LLVM file | Vastitas input | What to read in the IR | Closed theorem in `Vastitas.LLVMCorpus` |
| --- | --- | --- | --- |
| [exit-status.ll](../src/exit-status.ll) · 374 bytes | [ExitStatus.vast](../fixtures/ExitStatus.vast) | A signed literal, −(2¹²⁸+1), stays unbounded through both MidIR phases. At the C entry point its residue modulo 256 gives `ret i32 u0xFF`. | `exit_status_verified` |
| [folded-arithmetic.ll](../src/folded-arithmetic.ll) · 374 bytes | [FoldedArithmetic.vast](../fixtures/FoldedArithmetic.vast) | The source selects division for the ordered operands `(Nat, Int)`. Its Euclidean quotient for 7 and −3 is −2. Adding 12 gives the constant returned by `ret i32 u0x0A`. | `folded_arithmetic_verified` |
| [boxed-program.ll](../src/boxed-program.ll) · 1,830 bytes | [BoxedProgram.vast](../fixtures/BoxedProgram.vast) | Four functions pass a borrowed heap integer through an identity, doubling and mixed division. The hosted entry initializes the runtime and consumes the owned result. | `boxed_program_verified` |
| [ordered-calls.ll](../src/ordered-calls.ll) · 2,311 bytes | [OrderedCalls.vast](../fixtures/OrderedCalls.vast) | Two nested calls supply the left and right operands of an assembled subtraction method. The entry returns 23. | `ordered_calls_verified` |
| [assembled-conversion.ll](../src/assembled-conversion.ll) · 1,376 bytes | [AssembledConversion.vast](../fixtures/AssembledConversion.vast) | An assembled `Nat → Int` method returns 2¹²⁸ + 43. Its sibling of the same signature returns zero. | `assembled_conversion_verified` |
| [assembled-negation.ll](../src/assembled-negation.ll) · 1,389 bytes | [AssembledNegation.vast](../fixtures/AssembledNegation.vast) | The selected method negates a boxed integer larger than 2¹²⁸. The module retains the identity sibling. | `assembled_negation_verified` |
| [selected-projection.ll](../src/selected-projection.ll) · 1,968 bytes | [SelectedProjection.vast](../fixtures/SelectedProjection.vast) | The assembled scalar method constructs `pair(7, 19)` and calls the second-field function. Its retained sibling calls the first. | `selected_projection_verified` |
| [boxed-pairs.ll](../src/boxed-pairs.ll) · 4,157 bytes | [BoxedPairs.vast](../fixtures/BoxedPairs.vast) | Five functions construct and project homogeneous integer pairs. The selected method returns the large negative integer in its first field. Swapping the fields gives 42 at the entry. | `boxed_pairs_verified` |
| [singleton-power.ll](../src/singleton-power.ll) · 1,977 bytes | [SingletonPower.vast](../fixtures/SingletonPower.vast) | One function squares a boxed integer eight times, divides by seven and passes the owned quotient to the hosted entry. | `singleton_power_verified` |
| [borrowed-operator.ll](../src/borrowed-operator.ll) · 2,051 bytes | [Borrowed operator package](../fixtures/borrowed-operator/Vastitas.toml) | The caller borrows an edit grant on the imported family. Its selected implementation adds 40 and 2. The module also contains four unselected specializations of the method that returns zero. | `borrowed_operator_verified` |
| [uncalled-operator.ll](../src/uncalled-operator.ll) · 1,829 bytes | [Uncalled operator package](../fixtures/uncalled-operator/Vastitas.toml) | The entry returns 7. Sealing the borrowed family retains its addition method and four fallback specializations. | `uncalled_operator_verified` |
| [assembled-comparison.ll](../src/assembled-comparison.ll) · 2,382 bytes | [ComparisonMethod.vast](../fixtures/ComparisonMethod.vast) | The selected method compares two boxed integers and returns an `i32` Boolean. A branch passes 42 or 7 to a pointer `phi`. Each taken edge retains its boxed arguments and releases its owned temporaries. | `assembled_comparison_verified` |
| [bool-comparison.ll](../src/bool-comparison.ll) · 4,254 bytes | [BoolComparison.vast](../fixtures/BoolComparison.vast) | Four calls exercise the complete Boolean truth table. Assembly selects equality or inequality, giving the integer 2^128 + 10 or 2^128 + 7. The retained module selects equality. | `bool_comparison_verified` |
| [integer-predicate.ll](../src/integer-predicate.ll) · 873 bytes | [IntegerPredicate.vast](../fixtures/IntegerPredicate.vast) | Subtracts 256 from the first boxed integer, compares it with the second, releases both owned temporaries and returns a 32-bit Boolean. | `integer_predicate_verified` |
| [boxed-arithmetic.ll](../src/boxed-arithmetic.ll) · 1,021 bytes | [BoxedArithmetic.vast](../fixtures/BoxedArithmetic.vast) | The two borrowed arguments determine the result. The function subtracts 5 from the Nat, divides by the Int, adds the quotient to itself, releases three intermediate references and returns an owned Int. | `boxed_arithmetic_verified` |
| [assembled-bool.ll](../src/assembled-bool.ll) · 688 bytes | [AssembledBool.vast](../fixtures/AssembledBool.vast) | `main` calls the selected Boolean method and branches on the result. The two incoming edges supply 42 and 7 to the `phi`. The selected contribution returns its argument. The nonselected method also has a definition and returns false. | `assembled_bool_verified` |
| [literal-comparison.ll](../src/literal-comparison.ll) · 924 bytes | [LiteralComparison.vast](../fixtures/LiteralComparison.vast) | The selected method distinguishes −(2¹²⁸+1) from −1. The fallback compares 0 with 256. Both pairs share their low byte. The two Boolean results survive in separate methods. | `literal_comparison_verified` |
| [finite-projection.ll](../src/finite-projection.ll) · 802 bytes | [FiniteProjection.vast](../fixtures/FiniteProjection.vast) | The finite model and object select one specialization. Its two Boolean parameters remain in SSA, and returning the first selects exit 42. | `finite_projection_verified` |
| [static-selection.ll](../src/static-selection.ll) · 1,448 bytes | [StaticSelection.vast](../fixtures/StaticSelection.vast) | The assembled method passes through `keep`. Two specializations of `invoke` call distinct targets with the same Boolean argument. The method returns true and the lambda returns false, so the entry selects 42. | `static_selection_verified` |
| [structured-lookup.ll](../src/structured-lookup.ll) · 2,623 bytes | [StructuredLookup.vast](../fixtures/StructuredLookup.vast) | A 2 × 3 × 2 table maps three nominal tags to digit 9. A nullary table supplies the expected digit. The selected method uses `!a || b`, and the other method retains `!a && !b`. | `structured_lookup_verified` |
| [structured-lookup-linux-x86_64.ll](../src/structured-lookup-linux-x86_64.ll) · 2,647 bytes | [StructuredLookup.vast](../fixtures/StructuredLookup.vast) | The Linux target and data layout are part of the byte proof. The table, both Boolean methods, calls, branch and phi have the same model as the macOS file. | `structured_lookup_linux_verified` |
| [empty-lookup.ll](../src/empty-lookup.ll) · 439 bytes | [EmptyLookup.vast](../fixtures/EmptyLookup.vast) | The input carrier is empty. The switch has only a default edge. Every foreign `i32` returns `-1`. | `empty_lookup_verified` |
| [closure-unit.ll](../src/closure-unit.ll) · 549 bytes | [ClosureUnit.vast](../fixtures/ClosureUnit.vast) | The unit of the closure Monad on `lo < hi` returns the nonidentity arrow `up` at `lo` and the identity of `hi` at `hi`. The resulting arrow ordinals are 1 and 2. | `closure_unit_verified` |
| [float-identity.ll](../src/float-identity.ll) · 2,821 bytes | [Real identity](../../examples/packages/float-identity/src/main.vast) | The two-element binary64 buffer carries a negative zero and a signaling NaN through a single copy. Every call checks its status. | `real_identity_verified` |
| [float-complex-identity.ll](../src/float-complex-identity.ll) · 2,821 bytes | [Complex identity](../../examples/packages/float-complex-identity/src/main.vast) | The complex tag selects two binary64 components. Each store and expect receives both bit strings, including a subnormal imaginary component. | `complex_identity_verified` |
| [float32-identity.ll](../src/float32-identity.ll) · 2,785 bytes | [Real binary32 identity](../fixtures/float32-identity/main.vast) | Tag 2 selects binary32. The written negative zero and signaling NaN reach the store and expect calls as integer operands. | `real32_identity_verified` |
| [float32-complex-identity.ll](../src/float32-complex-identity.ll) · 2,785 bytes | [Complex binary32 identity](../fixtures/float32-complex-identity/main.vast) | Tag 3 carries both components. The first imaginary component is the smallest positive subnormal. | `complex32_identity_verified` |
| [tensor-column.ll](../src/tensor-column.ll) · 3,350 bytes | [Complex matrix–column contraction](../fixtures/tensor-column/src/product/mod.vast) | A 2×3 matrix times a column in `F32<CC>`. One bilinear GEMM call produces 33+6i in each of two checked cells. |
| [gemm-coefficients.ll](../src/gemm-coefficients.ll) · 4,293 bytes | [Scaled products](../../examples/packages/numerical/gemm-coefficients/main.vast) | Two binary64 products compute 3 and 30. The first call uses literal alpha and the second reads alpha from a live allocation. Each result is checked before the next write. | `gemm_coefficients_verified` |
| [opposite-s3.ll](../src/opposite-s3.ll) · 5,452 bytes | [Permutation inversion](../fixtures/opposite-s3/main.vast) | Two 36-row switches encode composition of the six permutations in reversed and original order. A six-row switch calculates the inverse. The entry distinguishes the two products and exits with 42. | `opposite_s3_verified` |
| [finite-iso.ll](../src/finite-iso.ll) · 2,515 bytes | [Two-object isomorphism](../fixtures/finite-iso/main.vast) | Two nullary lookups select arrows with opposite endpoints. Two composition functions check the inverse equations. The nested joins each have two predecessors. | `finite_iso_verified` |
| [finite-kleisli.ll](../src/finite-kleisli.ll) · 4,463 bytes | [Finite Kleisli package](../../examples/packages/finite-kleisli/Vastitas.toml) | The real application calls `unit`, `bind`, `compose`, `lift` and `mappedUp`. Its five equalities combine in four `and i1` instructions, then a branch and phi choose exit status 0 or 1. | `finite_kleisli_verified` |
| [kleisli-callback.ll](../src/kleisli-callback.ll) · 2,434 bytes | [Kleisli callback](../fixtures/kleisli-callback/main.vast) | The specialization of `applyArrow` calls the capture-free producer once, then passes its arrow ordinal to `bind`. Both the unit and multiplication of the selected Monad are the nonidentity element of the group of order two. | `kleisli_callback_verified` |
| [kleisli-forward.ll](../src/kleisli-forward.ll) · 2,456 bytes | [Direct Kleisli operand](../fixtures/kleisli-forward/main.vast) | The application passes the imported producer to `bind(p, k)`. In `@f2`, the erased function value occupies one `i1` instruction, then the calls to `@f0` and `@f1` use the same order as the explicit invocation above. | `kleisli_forward_verified` |
| [kleisli-forward-linux-x86_64.ll](../src/kleisli-forward-linux-x86_64.ll) · 2,480 bytes | [Direct Kleisli operand](../fixtures/kleisli-forward/main.vast) | The Linux triple and data layout select this printout. The specialized caller evaluates the same producer once and passes its ordinal to the same method. | `kleisli_forward_linux_verified` |
| [unary-table.ll](../src/unary-table.ll) · 604 bytes | [TableComparison.vast](../../experiments/compiler_validation/llvm/TableComparison.vast) | Cases follow the carrier's declaration order. Input ordinals 0, 1, 2 return 1, 0, 1, even though the source table lists its third row first. Other inputs return `-1`. | `unary_table_verified` |
| [s3-composition.ll](../src/s3-composition.ll) · 2,621 bytes | [S3Composition.vast](../fixtures/S3Composition.vast) | Two independently checked ordinals index the composition on six permutations. Row 1, column 2 gives ordinal 4. Reversing the inputs gives 3. | `s3_composition_verified` |
| [static-call.ll](../src/static-call.ll) · 709 bytes | [CallComparison.vast](../../experiments/compiler_validation/llvm/CallComparison.vast) | The module defines the lookup and a second export, `@vq_forward`. Its single `call i32 @vq_lookup(i32 %tag)` passes the original tag and returns the result. | `static_call_verified` |

Each file can be read or assembled independently. The 29 entry modules export `i32 @main()`. Four unary libraries export `i32 @vq_lookup(i32)`. The binary library exports `i32 @vq_lookup2(i32, i32)`. The call example also exports `i32 @vq_forward(i32)`. The two exact libraries export `ptr @vq_exact(ptr, ptr)` for arithmetic and `i32 @vq_exact(ptr, ptr)` for the predicate. Their signature comments identify the mathematical argument and result types.

The printer spells each target-header byte as an LLVM hexadecimal escape (for example, `\61` is `a`). Within the switch, `u0x0002` is the unsigned ordinal 2. The `i32 -1` at `%miss` has the unsigned value 4,294,967,295.

For each of the eleven public emission cases, `Output.decodes_iff` relates
its model parser to the complete UTF-8 buffer passed to the driver. A second
buffer parses to that model exactly when its bytes equal the published bytes.
The native regression changes `choose(true)` to `choose(false)`. Each program
passes the public compiler and gives its own exit value, 42 or 7. Their LLVM
modules differ only in the one-byte Boolean call argument. The handoff test
supplies each module as the other's readback and requires rejection before an
object is created. [Emission and readback theorem](../../lean-kernel/VastitasKernel/LLVM/Emission.lean) · [Native handoff regression](../check_exact_native.py)

The table's nominal input and output types are checked before lowering to the foreign `i32` ABI. The general `correspondence` theorems connect the selected Core function and both MidIR phases to the parsed module for every in-domain ordinal. Their `foreign_miss` theorems cover out-of-domain inputs. For the empty carrier, the latter theorem covers all 32-bit words. [Unary function theorems](../../lean/VastitasOracle/UnaryFunction.lean) · [Static call theorems](../../lean/VastitasOracle/CallFunction.lean)

The boxed library requires an initialized Lean runtime and the versioned C shim. Its SSA registers hold Lean objects. A native caller supplies the declared Nat/Int kinds. The abstract call semantics assign no result to an ill-typed arithmetic call. The artifact checks the exported owner, specialization, operand types and current revision. Replay exchanges each operator spelling with its named-call spelling and compares all three protected family IDs and ordered operand keys. Both forms produce the same 1,021 bytes. Its parser reconstructs the exact calls and requires the canonical reference-counting instructions. The Oracle proves that the parsed model recovers the execution MidIR block and has the same return observation as both MidIR phases for every argument list under the shim contract. [Shim source](../runtime/exact.c) · [Oracle correspondence](../../lean/VastitasOracle/ExactLibrary.lean)

## Replay

Run from the repository root with the pinned Rust and Lean toolchains and the project's build dependencies.

```sh
python3 llvm/check.py
```

The runner builds the proof dependencies and checks each registered theorem against the retained file. It then uses the original manifests and dependencies for the three Kleisli applications and the borrowed-operator package, places each standalone source in its edition 2026 package, and runs the public `vastitas check --llvm-preview --target-triple TRIPLE --data-layout LAYOUT`. The compiled Lean checker checks the protocol 10 input, constructs the Core and both MidIR phases, and parses the full canonical UTF-8 output back to the modeled module. The runner compares stdout byte for byte with the retained file and checks that every file has a source fixture and a named proof. Replay requires the project toolchains and can run without libLLVM. [Replay runner](../check.py) · [Emission checker](../../lean-kernel/VastitasKernel/LLVM/Emission.lean) · [Exit correspondence](../../lean/VastitasOracle/ExitFunction.lean)

Machine-code generation and execution have separate evidence. On macOS arm64 the pinned LLVM 23.1.4 experiment parsed the unary and two-function modules, emitted objects and checked their results. Its empty-table boundary test exercised the same 439-byte module on 4,098 foreign inputs. Native execution and LLVM's verifier are outside the Lean byte theorem. [Table qualification](../../experiments/compiler_validation/llvm/results/macos-arm64/unary-table.json) · [Call qualification](../../experiments/compiler_validation/llvm/results/macos-arm64/static-call.json)

On Linux x86-64 and macOS arm64 the pinned libLLVM adapter produced objects for 15 public boxed libraries. All 121 calls matched a compiled Lean function and independent arbitrary-precision expectations. Cases cover every arithmetic signature, division by zero, both mixed operand orders and repeated SSA operands. A heap reference-count probe for each library checks the caller’s ownership before and after releasing the result. Binary operations on a single sort also receive the same heap object in both argument positions. To repeat this comparison after building the frontend, run `python3 llvm/check_exact_native.py --backend target/debug/vastitas-llvm-qualification` with the qualified adapter. On the same macOS host, LLVM 23.1.4 also emitted a 1,488-byte x86-64 ELF object from the Linux-targeted 1,045-byte quotient module. The Linux/macOS compiler CI job uses `--lean-clang` to exercise the same calls with the compiler bundled in the pinned Lean toolchain. [Native comparison](../check_exact_native.py) · [Two-host CI and artifacts](https://github.com/MGYamada/Vastitas/actions/runs/44871839008)

For the closure Monad, the public preview and replay of the full function revision produced identical bytes. LLVM 23.1.4 and an independent Lean program returned 1 and 2 on the two domain ordinals and the miss sentinel on 2, 3, 4095 and `UINT32_MAX`. The generated Lean/C executable checked both named arrows. The complete-byte handoff rejected a change to one result digit before object generation. [Closure unit qualification](../../experiments/compiler_validation/llvm/results/macos-arm64/closure-unit.json)

The two-argument library preserves the selected category, both argument fibers and the result fiber through Core and MidIR. Each `icmp ult` bounds one input before the multiplication and addition compute its row-major address. Both failed guards and the switch default return `-1`. The qualification compared all 36 ordered products with independent permutation composition and exercised 45 foreign inputs. Reversing the source operands changed the parameter order in the emitted function and passed a second run over all 81 pairs. Changing the guard, stride, branch condition or miss value failed the complete-byte checks. [Binary correspondence](../../lean/VastitasOracle/BinaryFunction.lean) · [S3 host run](../../experiments/compiler_validation/llvm/results/macos-arm64/s3-composition.json)

On macOS arm64 the public feature-enabled `build --llvm-preview` linked and installed both executables. The literal returned 255 and the folded arithmetic returned 10. Each object-generation control read all 374 bytes of its own module and produced a 512-byte object. The generated Lean/C executables and the independent Lean expressions gave the same two exit codes. The kernel response identifies the compiled checker. Per-input Official and Fast proof checking are separate release obligations. [Literal qualification](../../experiments/compiler_validation/llvm/results/macos-arm64/exit-status.json) · [Arithmetic qualification](../../experiments/compiler_validation/llvm/results/macos-arm64/folded-arithmetic.json) · [Release obligations](../../docs/v0.1.0-admission.md)

For the complete finite Kleisli application, LLVM 23.1.4 emitted a 2,760-byte object on macOS arm64. The hosted native build, an independently linked executable, the LLVM model and the Lean/C control all returned 0. Changing the first equality to inequality yielded 1. The variant that exercises `extend` produced 5,326 bytes of assembly and a 3,176-byte object. Its checked entry, both native executables, Lean/C and the independent Lean calculation returned 42. [Package qualification](../../experiments/compiler_validation/llvm/results/macos-arm64/finite-kleisli.json)

The assembled executable returned 42 in the macOS arm64 LLVM build, the separately linked 912-byte object, the generated Lean/C build and the independent Lean program. Its three Core symbols and the selected contribution are recorded alongside the complete-byte comparison. [Assembly qualification](../../experiments/compiler_validation/llvm/results/macos-arm64/assembled-bool.json)

For a folded entry, Lean evaluates the original closed Core expression, checks the ordered operator sites and their unique protected methods, and connects the result to both MidIR phases and the returned bytes. The hand-written runtime ABI fixture separately exercises Nat, Int, branches and runtime calls. [Fold correspondence](../../lean/VastitasOracle/ExitFunction.lean) · [Core evaluation](../../lean/VastitasOracle/ExactFold.lean) · [Runtime ABI fixture](../../experiments/compiler_validation/llvm/results/macos-arm64/program.ll)

## Comparison with Lean's LLVM emitter

Lean 4.35.0's `emitCtor` allocates the constructor and sets its object fields in declaration order. Its `emitProj` reads a field by index. Vastitas uses tag zero and two object fields for both integer pair types. The versioned construction shim retains each borrowed field, including when both slots refer to the same heap integer. The projection shim retains its result before returning it. The macOS arm64 native test compares both exported swaps with a separately compiled Lean `Prod` swap. It checks distinct heap integers, repeated references and immediate values. The C probe checks each heap object's reference count after releasing the argument and again after releasing the result. [Pinned constructor emission](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L587-L608) · [Pinned projection emission](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L795-L812) · [Ownership probe](../fixtures/PairOwnership.c)

The singleton power example passes the same borrowed pointer twice to each of its eight multiplications. The division returns a 403-bit quotient. Vastitas releases ten SSA temporaries in reverse order before returning the quotient. In the Lean 4.35.0 control, generated C calls `lean_int_mul` eight times, releases each previous square after its last use and calls `lean_int_ediv`. Both executables return 219. A second link of the same object borrows its quotient before the production exit function consumes it. The probe accepts the full quotient and distinguishes a value larger by 256, which has the same exit status. Upstream `emitDec` emits the reference-count instruction supplied by Lean IR. This installation requires a build with `-DLLVM=ON` to produce upstream bitcode. [Pinned emitDec](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L619-L624) · [Native comparison](../check_exact_native.py)

For a nullary table on the carrier `Bit { lo; hi; }`, changing the written row
from `() => hi` to `() => lo` changes one byte in its 876-byte arm64 module.
The selected switch case returns ordinal 1 or 0. The caller compares that
ordinal and joins the two branches with an `i32 phi`. The two LLVM executables,
the generated Lean/C executables and an independent Lean control returned 42
and 7. Lean 4.35.0's `emitCase` zero-extends a discriminant for its switch,
and `emitJmp` writes join arguments to slots. Direct bitcode generation on
the comparison toolchain requires `-DLLVM=ON`. [Physical table regression](../../tests/finite_tables.rs) · [Pinned emitCase](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L1104-L1126) · [Pinned emitJmp](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L1050-L1065)

A finite-indexed Boolean function can return either of its two parameters. For
the same index specialization and arguments `(true, false)`, changing the body
from `{ b }` to `{ q }` changes a single byte in the 802-byte arm64 module. The return instruction
`ret i1 %v0_0` becomes `ret i1 %v0_1`. Lean 4.35.0's `FnBody.ret` calls
`emitArgVal` to load the selected argument from its slot, then passes it to
`LLVM.buildRet`. The revision-matched llvm-sys executables, the generated
Lean/C controls and an independent Lean program returned 42 and 7,
respectively. The second source rejected the first revision before emitting
bytes. Direct Lean bitcode generation required a toolchain built with
`-DLLVM=ON`.
[Finite function regression](../../tests/finite_binders.rs) · [Pinned argument load](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L576-L581) · [Pinned return](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L1176-L1178)

In the structured lookup module, the helper for the three-axis table appears before `@f0`. Both calls to the selected `choose` method target `@f1`. The nullary table helper appears before the caller `@f2`, and the retained fallback is `@f3`. Lean proves the helper and body order for the entire finite module and relates the selected method to its Core specialization under the same revision. Each parsed body block has exactly the calls of its execution MidIR block, with the same callee, result register, operand order and ABI widths. Swapping the two live `i1` operands of the second `@f1` call still parses and changes the modeled exit from 42 to 7 on both targets. Replacing the first operand’s width with `i32` fails to parse. Lean 4.35.0’s `emitFullApp` looks up the callee by `FunId`, loads the arguments in order and emits a typed call for this nonempty argument list. [Vastitas block proof](../../lean/VastitasOracle/FiniteCalls.lean) · [Operand replay](../fixtures/StructuredCallOrder.lean) · [Finite module proof](../../lean/VastitasOracle/FiniteProgram.lean) · [Lean direct calls](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L755-L773)

In the structured lookup, three unsigned comparisons guard the row-major index `(row * 3 + column) * 2 + bit`. The nullary table switches on the literal zero. Lean 4.35.0's `emitCase` zero-extends one discriminant to `i64` before building its switch. Here the closed function takes three `i32` parameters and switches on their checked `i32` index. The Lean control computes the digit from constructor cases. It returned 42 for the selected method and 7 for the fallback, as did the two Vastitas modules compiled with Apple Clang 21.0.0 using its host target header. Generating bitcode with `lean -b` stopped at the toolchain’s LLVM build check, so the comparison uses the pinned emitter source. [Structured lookup IR](../src/structured-lookup.ll) · [Lean comparison](../../experiments/compiler_validation/llvm/StructuredLookupComparison.lean) · [Pinned emitCase](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L1104-L1127)

LLVM 23.1.4 assembled and verified the retained 2,623 bytes on macOS arm64. The 1,416-byte object linked and returned 42. A separate copy with test wrappers exercised all 12 valid coordinates, 68 out-of-range tuples, both Boolean methods on all four input pairs and the nullary result 9. The public llvm-sys build returned 42 with the original function revision. Changing the selected predicate or one table row gave exit 7 with its own revision. Both changes caused the build to reject the original revision before installing an executable. [Public package regressions](../../tests/llvm_package_roots.rs) · [Lean model regressions](../../lean-kernel/VastitasKernel/LLVM/FiniteModuleRegression.lean)

For the x86-64 Linux replay, Clang 23.1.4 supplied the triple `x86_64-unknown-linux-gnu` and its data layout. Passing both to the public checker produced 2,647 bytes. LLVM 23.1.4 assembled and verified them on macOS, and `llc -filetype=obj` produced a 2,120-byte ELF64 relocatable object with machine `EM_X86_64` and a defined `main`. One saved function revision reproduced both files, and the Lean model returned 42 for each. Changing either the selected method or its unselected sibling invalidated the saved revision on both targets. Linux-host linking and execution of this sample remain open. In Lean 4.35.0, `toLLVMType` maps `usize` through `size_tType`, which returns `i64`. This sample uses only `i1` and `i32`; the closed theorem includes the complete target header. [Linux IR](../src/structured-lookup-linux-x86_64.ll) · [Pinned type mapping](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L331-L342) · [Pinned size_tType](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L41-L43)

In the literal-comparison example, the call to `@f0` passes one Boolean. Its method combines the argument with the folded result using `and i1`. The caller's branch joins the two exit codes with a phi. Lean 4.35.0’s `emitFullApp` loads arguments from slots for its direct call. Its `emitJmp` stores arguments into the join-point slots before branching. The comparison uses the pinned emitter source. The two native runs exercise Vastitas LLVM and the Lean/C backend. [Pinned call emission](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L755-L773) · [Pinned join emission](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L1050-L1060) · [Oracle comparison theorem](../../lean/VastitasOracle/ExactFold.lean) · [Native regression](../../tests/llvm_preview.rs)

For an argument of type `Fn<Bool, Bool>`, the static selection example specializes `invoke` twice. In the retained LLVM, `@f2` calls the assembled method `@f1` and `@f4` calls the lifted lambda `@f3`. The call to `keep` remains in evaluation order. On macOS arm64, LLVM 23.1.4 assembled and verified the retained bytes and emitted an object that linked and returned 42. Changing only the selected method to return false produced exit 7. In Lean 4.35.0, `emitFullApp` generates a direct typed call for a known function with arguments. For a function value held in a variable, `emitApp` calls the runtime's `lean_apply_N` or `lean_apply_m` with the closure and its arguments. This comparison uses the upstream emitter source. [Static selection IR](../src/static-selection.ll) · [Pinned emitApp and emitFullApp](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L726-L768)

The finite callback example passes `next` as a value of type `Fn<(), Hom<C, Obj::o, Obj::o>>`. Its specialization `@f2` takes just the input arrow. It calls the nullary `@f0`, then passes that result to `@f1` as its second operand. LLVM 23.1.4 verified the retained module on macOS arm64 and emitted a 1,832-byte object. The separately linked object, the public `build --llvm-preview` with the expected function revision, and the Lean/C build all returned 42. Changing only the producer from `C::s` to `C::e` changed all three exits to 7. In the pinned Lean emitter, `emitApp` constructs an arity-specific runtime application for a variable callee with few arguments. Its `emitFullApp` branch for known nullary declarations loads the declaration value. The comparison here follows those source branches. [Callback IR](../src/kleisli-callback.ll) · [Pinned emitApp and emitFullApp](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L727-L771)

In the direct forwarding fixture the caller supplies a function from another package. The checked revision records its defining package and Hom result, the selected Monad, all three object indices, the forwarding declaration and its call site. Replay changes the recorded method span, the producer position and the model separately. Each change must fail before any IR bytes are returned. On macOS arm64, LLVM 23.1.4 assembled and verified the 2,456-byte file and emitted a 1,832-byte object. Linking that object, building through the public llvm-sys preview with the expected revision, and building with Lean/C each gave exit 42. Changing the producer to return the identity gave exit 7 on all three paths. The pinned Lean emitter's variable-application path passes the closure to a runtime function. Here the statically known producer has a direct nullary call and `bind` takes two arrow ordinals. [Direct forwarding IR](../src/kleisli-forward.ll) · [Pinned Lean application lowering](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L727-L771)

The x86-64 Linux forwarding module has the same 2,129 body bytes as its macOS arm64 counterpart. Disassembling with LLVM 23.1.4 gives a call to `@f0()` followed by `@f1(i32 %v0_0, i32 %v0_2)`, where `%v0_2` holds the producer result. On macOS the cross-target `llc` emitted a 2,104-byte ELF object. The host-native workflow tests both producer results with the host triple and linker. [Linux assembly](../src/kleisli-forward-linux-x86_64.ll) · [Native test](../../tests/finite_monads.rs)

Lean 4.35.0's `emitCase` zero-extends the tag to `i64` and builds a switch with a default block. The corpus exposes `i32` ordinals and specifies the result of its default block. The two-argument S3 switch first checks both Hom ordinals, then branches on their joint row-major index. Its MidIR lookup reads the two SSA operands in source order. The Oracle proves that reading these slots gives the Core lookup for every slot assignment, including a missing operand. Lean's `emitCase` switches on the tag of a single discriminant. In `emitFullApp`, Lean resolves the callee, loads operands from slots, builds the typed call and stores its result. The corpus's forwarder uses its SSA parameter and returns the call result directly. The pinned Lean installation reported no LLVM feature, so the available upstream comparison is with the emitter source. [Finite lookup proof](../../lean/VastitasOracle/FiniteOpcodeCoverage.lean) · [Pinned emitCase](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L1104) · [Pinned emitFullApp](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L755)

The hosted integer sample keeps the three direct calls between its four Vastitas functions. The borrowed identity retains its parameter once. The caller drops its temporary after the add. Lean 4.35.0's `emitFullApp` also emits calls to known declarations. Its `emitMainFn` initializes the runtime and handles Lean module and IO entry conventions. The Vastitas entry needs only the integer runtime and a final Euclidean remainder modulo 256. On macOS arm64 the native executables with divisors 3, 0 and 1 returned 84, 0 and 254. The comparison harness builds the corresponding Lean functions with `@[noinline]` and checks the same process statuses against Python integer arithmetic. In the generated C, `l_twice` calls `l_keep` before `lean_int_add`, and `l_quotient` calls `lean_int_ediv`. An assembled variant returns 42 and rejects a saved revision that substitutes the other method of the same family and ABI. For the x86-64 Linux target the checked source produced 1,854 bytes and LLVM 23.1.4 emitted a 2,240-byte ELF object on this macOS host. Native execution was measured on macOS. [Pinned entry emitter](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L1488-L1534) · [Hosted comparison](../check_exact_native.py)

In the borrowed-operator package the family belongs to `edit_base` and the selected contribution belongs to `edit_addon`. The caller `@vq_f1` passes two boxed integers to `@vq_f0`. The unselected `@vq_f5` has the same signature and returns zero. Substituting its definition and Core symbol in the receipt makes the public emitter return `E_FUNCTION_REVISION` before writing bytes. The macOS arm64 executable and its Lean-generated C control both returned 42. The C control calls `l_chosen`, which calls `lean_int_add`. In Lean 4.35.0, `emitFullApp` loads each argument from its slot before emitting the typed direct call. Here the call uses the two SSA operands directly. The installed Lean toolchain reported no LLVM feature and produced no bitcode for this control. [LLVM file](../src/borrowed-operator.ll) · [Pinned call lowering](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L755-L774)

Changing the defining package version from 0.1.0 to 0.2.0 in its manifest gives the family a different ID. Both revisions emit the same 2,051 bytes, including the call to `@vq_f0` with the two operands in source order. The macOS arm64 LLVM and Lean/C executables returned 42 for both versions. Replaying the old revision for the new version fails before linking. Lean 4.35.0’s `emitFullApp` looks up its function ID and loads each argument in order for the typed call. [Owner regression](../../tests/function_revision.rs) · [Pinned call emission](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L755-L774)

The uncalled-operator package seals the same family. Its hosted entry calls only the function returning 7. The LLVM module retains all five method specializations, including the checked integer addition. Lean 4.35.0's `emitFns` traverses the declarations supplied by its IR environment. Vastitas obtains its declaration set from the checked package, including families the root explicitly sealed. [LLVM file](../src/uncalled-operator.ll) · [Lean declaration emission](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L1252-L1263)

The per-input certificate for the hosted boxed example uses the same typed call graph. The driver captures the function revision, the ordered physical inputs, every header and instruction byte, and the full integer before the exit projection. The Lean statement compares the two header lines and each body line, including operand order, retains, releases and final newline. Official replays the complete certificate in an empty Lean kernel environment. Fast receives the same export and checks it with nanoda. A separate two-function example checks this boundary with `--lib` and a manifest dependency. Changing only a comment preserves its direct call and all 1,127 LLVM bytes, and makes the saved certificate stale. [Certificate and reproduction](../../experiments/compiler_validation/boxed_certificate/README.md)

For the boxed quotient, the C generated by Lean 4.35.0 calls `lean_nat_sub`, `lean_nat_to_int`, `lean_int_ediv` and `lean_int_add` in that order. The two add operands are the same quotient. The Vastitas LLVM file calls the mixed division shim with a borrowed numerator. The shim retains the Nat before the consuming conversion and releases the converted reference after division. In the upstream emitter, `emitFullApp` obtains arguments from local slots and `emitInc` and `emitDec` emit refcount calls. On this toolchain `lean -b` requested a build with `-DLLVM=ON` and produced no bitcode for disassembly. [Pinned reference counting](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L610-L624) · [Pinned calls](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L755-L774)

The mixed division in `boxed-arithmetic.ll` calls `vastitas_nat_int_div_v1`. For the ordered key `(Nat, Int)`, the checked revision records method 1 of `std::operator::div` and result `Int`. Reversing the operand types selects method 2. The real kernel rejects a saved revision with those ordinals exchanged. Lean 4.35.0's `emitFullApp` gets the function type from its selected function ID and loads each argument in order before emitting the call. [Boxed arithmetic IR](../src/boxed-arithmetic.ll) · [Method revision regression](../../tests/exact_operators.rs) · [Pinned call emission](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L755-L774)

Vastitas appends a nullary SSA instruction for each nested Unit, Bool, Nat or Int literal. Its Core constructor, opcode tag, result slot and value in both phases are checked by the Oracle. Lean 4.35.0 supplies its IR type to `emitLit` and stores the value in the selected slot. The comparison below follows its numeric cases through emission. [Literal lowering theorem](../../lean/VastitasOracle/LiteralCoverage.lean) · [Pinned literal emitter](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L777-L783)

For an object-valued Nat literal, Lean's `emitNumLit` calls `lean_unsigned_to_nat` when the literal fits a `UInt32` and `lean_cstr_to_nat` for larger literals. In the Vastitas arithmetic sample the checker already knows both operands of division and the addend. It verifies the selected methods and their exact integer results before printing the single `ret i32 u0x0A`. This sample measures a folded computation. The runtime ABI comparison covers calls with live integer operands. [Pinned emitNumLit](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L626) · [Runtime ABI comparison](../../experiments/compiler_validation/llvm/README.md)

For a jump to a join point, Lean's `emitJmp` checks the number of arguments, writes each incoming value to the formal parameter's slot and branches. The assembled Boolean example uses an `i1` call and branch. Its exit block reads a single `i32 phi` with an incoming value from each predecessor. The correspondence theorem identifies the checked winner and contribution. A second theorem covers both Boolean inputs for every method body in the module. [Pinned emitJmp](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L1050) · [Dispatch theorems](../../lean/VastitasOracle/DispatchFunction.lean)

Compiling the same source in a package with an unused indexed marker in
a dependency reproduces all 688 bytes of `assembled-bool.ll` for the pinned
macOS arm64 header. Three valid manifest spellings give identical bytes,
including the call to the selected Boolean method and both predecessors of the `i32 phi`. Replaying
the revision from the first spelling against either other spelling fails
because the physical manifest text belongs to the revision.
[Manifest and LLVM regression](../../tests/protocol_epoch.rs)

Two edition 2026 packages give `Cold` and `Warm` opposite parent orders. Both
use the same `Bool` dispatch key and assemble the same two methods. The more
specific method returns true in one package and false in the other. In each
532-byte reference module, `@main` calls `@vq_selected` and the two edges of
an `i32 phi` supply 42 and 7. The macOS arm64 executables produced by libLLVM
and by the Lean/C path returned 42 and 7 for their respective packages.
Changing only the decoded hierarchy now fails at the original selector span.
Lean 4.35.0's `emitFullApp` resolves the callee by function ID and its
`emitJmp` writes join arguments to slots before branching.
[Public and native regression](../../tests/llvm_preview.rs) · [Pinned call emission](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L755-L774) · [Pinned join emission](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L1050-L1060)

The finite Kleisli application has six linked Core functions and eight finite-table helpers. Its hosted `@main` calls `@f5`, which calls the five other functions. The typed Hom fibers in this example are singletons, so their sole legal tag has ordinal 0. The public link records the original Core symbols and the four specializations of the optional `monad::kleisli` package. The package qualification includes a separate variant that calls `extend` on the named `Triple`. In that variant, `@f4` calls `@t4_0_2` with its arrow argument, then calls `@t4_0_3` with the multiplication ordinal followed by the mapped arrow. The report retains the complete seven-line function body and the checked table identities. Lean's `emitFullApp` loads arguments from slots before a typed call, and its `emitCase` builds a switch for a single tag. Both Vastitas helpers switch on an `i32` ordinal. [Package qualification](../../experiments/compiler_validation/llvm/results/macos-arm64/finite-kleisli.json) · [Closed entry semantics](../../lean/VastitasOracle/PackageLink.lean) · [Pinned emitFullApp](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L755) · [Pinned emitCase](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L1104)

Lean 4.35.0's `emitFullApp` looks up a resolved `FunId`. In the
nonempty-argument case it loads the arguments and calls `LLVM.buildCall2`.
The Vastitas namespace test imports one of two nullary integer functions under
the name `picked`. On its reference target both modules have 983 bytes. Each
contains a direct call to `@vq_f0`. Resolving the other import changes which
integer that function returns. The two macOS executables and their generated
Lean/C controls exit with 42 and 7. A wire-only substitution fails at the
written target, before LLVM emission. [Pinned call emission](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L755-L774) · [Namespace regressions](../../tests/namespaces.rs)

Lean 4.35.0's `hasMainFn` searches the IR environment for a declaration named
`main`. After emitting the functions and initializer, `emitMainFnIfNeeded`
uses that result to decide whether to build a host entry. Vastitas checks the
physical file of a flat `main` before either LLVM action. Moving the name to
a `--lib` function and updating the wire to match every token and span yields
`E_LIBRARY`. Both actions emit bytes for the original entry. In the signed
literal example, changing the final digit of the magnitude from 7 to 8
changes one of the 374 bytes. Both the LLVM 23.1.4 executable and the independent
Lean control exit with 255 for the first input and 254 for the second. Replaying
the first revision preserves the installed executable with exit status 255.
[Pinned entry selection](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L1603-L1616) · [Entry-file regression](../../tests/singleton_source.rs) · [Signed literal](../fixtures/ExitStatus.vast)

Lean's `emitMainFn` constructs an `i64` entry with arguments, initializes the Lean runtime, applies the user entry and handles its IO result. Its success path unboxes the returned `UInt32` and sign-extends to the host result. The literal-only Vastitas entry has no runtime dependencies and projects the unbounded result to the specified process exit status before printing the IR. The source comparison and the observed host exit status can be replayed separately. [Pinned emitMainFn](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L1488) · [Success result conversion](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L1583)

Lean 4.35 selects LLVM `float` for `IRType.float32` and `double` for `IRType.float`. Its constructor accessors also distinguish the two widths. Vastitas keeps precision and component count in the checked storage scalar. The adapter IR generated by Apple Clang 21.0.0 on macOS arm64 declares the real GEMM coefficient parameters as `float` for `cblas_sgemm` and `double` for `cblas_dgemm`. Both complex calls take pointers to interleaved coefficients at the selected width. The Vastitas module passes an arena pointer and 34 integer words to the checked GEMM adapter. The words carry the physical scalar, three matrix views, transpose and conjugation flags, write mode and both coefficient sources. [Pinned type mapping](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L331-L332) · [Pinned constructor accessors](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L837-L838)

The binary64 coefficient example first overwrites a cell with `0.5 × (2 × 3) = 3`. A second call reads alpha from a live allocation and accumulates `4 × (2 × 3) + 2 × 3 = 30`. The Lean 4.35.0 arithmetic control returns the same two bit patterns at each width. Its generated C takes scalar `float` and `double` arguments. The installed toolchain reports that its LLVM backend needs a build with `-DLLVM=ON`. The comparison harness disassembles its bitcode when the feature is available. [Lean control](../../experiments/compiler_validation/llvm/GemmComparison.lean) · [Stored LLVM](../src/gemm-coefficients.ll)

The public LLVM preview also executes eight forwarded map products across the four storage representations. In a binary32 complex matrix-column contraction, one adapter call carries both input conjugation flags as zero. The native entry checks that both result cells equal `33+6i`. A change to the contracted dual or surviving basis rejects the source before LLVM emission. [Public map regressions](../../tests/numerical_source.rs) · [Column contraction](../../tests/tree_source.rs)

For a runnable check of the component ABI, the Lean 4.35.0 control exported two functions with body `if select then x else y`. With `x = 1.5` and `y = 2.25`, `lean --run` returned the following bit patterns. The signatures come from `lean -c`. On the same installation `lean -b` requested a build with `-DLLVM=ON` and produced no bitcode.

| Lean arguments | Selection | Result bits | Exported C signature |
| --- | --- | --- | --- |
| `Bool`, `Float32`, `Float32` | `true` | `0x3fc00000` | `float vast_compare_choose32(uint8_t, float, float)` |
| `Bool`, `Float`, `Float` | `false` | `0x4002000000000000` | `double vast_compare_choose64(uint8_t, double, double)` |

The four `Affine(R, 2)` fixtures compare every byte of their LLVM module with the corresponding explicit `realize::<R>` identity at a fixed triple and layout. The fresh mathematical subject and its selected constructor appear in the function revision. Both sources reach the same storage copy and cleanup calls. Lean 4.35.0’s `emitFullApp` emits a call from the function and argument slots of its own IR. The comparison here is with that emitter source. [Wrapper regression](../../tests/numerical_realization.rs) · [Pinned call emission](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L755-L774)

In the real identity example, the physical declaration supplies the dimension and the order of the chart coordinates. Changing `Affine(2)[x, y]` to `Affine(2)[y, x]` while retaining the original wire fails at `y` before the storage copy can be emitted. Substituting `pullback(x -> x, y -> y)` for the written `identity` also fails before emission, even though the exact coordinate maps agree. [Physical chart and graph regressions](../../tests/numerical_realization.rs)

For the complex tensor-column fixture, the graph selects the matrix's dual
axis and the vector's primal axis. Its sole join uses the caller's output
buffer. The expected schedule constructs the two layouts, the four input
components and both expected results independently of the printer. Lean checks
all 3,350 bytes, including the F32 complex tag and the ordered external
call arguments. Lean 4.35.0's external-call emitter also follows parameter
order. The tensor axes and nonconjugating product are Vastitas source and
storage checks. [Pinned argument emission](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L656-L679) · [Complete bytes proof](../Corpus.lean)

Changing the linear implementation of the column fixture from complex to real
while keeping its complex buffers produces `E_TENSOR` before LLVM emission.
With matching real buffers and literals, the complete module is 3,314 bytes.
The first integer after the arena in the single `vq_storage_gemm` call changes
from 3 (`F32<CC>`) to 2 (`F32<RR>`). On macOS arm64 the LLVM 23.1.4 and
Lean/C executables linked with sequential LP64 OpenBLAS 0.3.34 both passed
the two cell checks in each program. The complex product gives 33+6i per cell and the
real product gives 9. Lean 4.35.0's `emitSimpleExternalCall` pairs parameters
with arguments in order and constructs the call type from the non-erased
parameters. In these Vastitas modules the storage ABI spells the representation
as an `i64` argument. [Physical declaration and ABI regression](../../tests/indexed_definition_source.rs) · [Pinned external-call emitter](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L656-L683)

The GEMM coefficient fixture has two read-only input buffers. For the Linux
x86-64 target the original source and a dimension spelled `0001` produce identical 4,317-byte
modules. Rebinding the left map to the second input changes exactly one ordered
buffer operand in each of the two `vq_storage_gemm` calls. On macOS arm64 the
original and the equivalent spelling exit 0. The redirected program exits 1 at
its original numerical expectation. Lean 4.35.0's `emitSimpleExternalCall`
builds the argument list in parameter order. Here the checked storage schedule
also supplies the concrete buffer number for each operand.
[Pinned external calls](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L656-L679) · [Public GEMM operand regression](../../tests/numerical_source.rs)

The contraction-tree example writes a 2 × 3 × 4 tensor into scratch storage
with shape 8 × 3 before its first GEMM. Its second packing step regroups the
2 × 4 × 5 intermediate from axis order `[0,1 | 2]` to `[0,2 | 1]`.
Lean 4.35.0's `emitSimpleExternalCall` constructs an LLVM function type and
passes arguments in declaration order. Vastitas passes an arena pointer, two
six-word physical views and the three dimensions to `vq_storage_pack3`.
`vq_storage_regroup3` also receives the input and output grouping codes,
48 and 42 for the intermediate. The storage checker supplies the allocation
IDs and verifies that the input and output bytes are disjoint. The C adapter
returns a status that selects the next LLVM block or the arena cleanup.
[Pinned external calls](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L656-L671) · [Contraction-tree source](../../examples/packages/numerical/contraction-tree/src/real/mod.vast) · [Public native regression](../../tests/tree_source.rs)

The physical return type of that resource entry is checked before LLVM emission.
Changing only `main() -> Int` to `main() -> Nat` in its saved protocol request
fails at the result type and produces no module. Lean 4.35.0's `emitFnDeclAux`
reads its result and parameter types from the Lean IR declaration when constructing
an LLVM function type. Vastitas checks resource signatures against the edition
source before the storage entry uses its fixed process ABI.
[Pinned function declaration](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L490-L517) · [Signature regression](../../tests/resource_value_source.rs)

The same GEMM program can return 0 or 7 after its successful cleanup.
Changing only the physical return literal in a saved request is rejected.
Regenerating the request changes just `ret i32 0` to `ret i32 7`. Each failure
edge still returns 1. The pinned Lean backend emits a return of the lowered
argument at `FnBody.ret`; the Vastitas storage entry returns the checked
process status after deleting its arena. [Pinned return emission](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L1176-L1178) · [Physical result regression](../../tests/resource_value_source.rs)

In the GEMM coefficient example, changing the first allocation from one element
to two changes just the final `i64` operand of its `vq_storage_allocate` call.
Both Linux x86-64 modules contain 4,317 bytes. Both macOS arm64 executables
pass the same GEMM expectations. Lean 4.35.0's `emitSimpleExternalCall`
pairs each argument with its parameter, skips erased parameters and builds a
typed external call. The Vastitas shim receives the arena, owner slot,
representation and element count in that order. [Pinned external call](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L656-L671) · [Allocation regression](../../tests/numerical_source.rs)

In the real and complex identity modules, `vq_storage_store` and `vq_storage_expect` receive integer constants for the IEEE components. Lean checks each physical cell statement, including its position in the resource function, before constructing these calls. Changing a sign-of-zero payload to the adjacent subnormal in the source and regenerating the request changes the call operands. Submitting the old wire with the edited source yields `E_RESOURCE_SOURCE`. The four width and carrier combinations run the same comparison. In Lean 4.35.0, `emitLit` allocates a slot for the declared IR type and uses `emitNumLit` for numeric literals. Vastitas passes the integer constants directly to the storage calls. [Pinned literal emission](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L777-L783) · [Cell regression](../../tests/numerical_realization.rs) · [Pinned typed call emission](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L755-L774)

For the two binary32 files, LLVM 23.1.4 assembled the 2,785 bytes and verified each module. Disassembly preserved the integer operands 2147483648 (negative zero) and 2139095106 (signaling NaN) in the two stores and expectations. The Linux x86-64 preview changed the header and kept the call bodies byte-identical. On the arm64 host, LLVM 23.1.4 `llc` produced two 1,968-byte ELF relocatable objects from those Linux modules. Running the UInt32 control under Lean 4.35.0 printed the same integers, and `lean -c` returned those constants from the two branches. On the tested arm64 toolchain, `lean -b` reported that it requires a build with `-DLLVM=ON`. Upstream `emitNumLit` uses `LLVM.constInt` for a numeric literal of an unboxed type. [UInt32 control](../fixtures/Float32ComponentControl.lean) · [Pinned numeric literal emission](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L626-L634)

The first `vq_storage_gemm` call in the scaled product module passes 4602678819172646912, the binary64 bits of `0x1p-1`. Regenerating the request with `0x1p-2` changes that argument to 4598175219545276416. On macOS arm64 the native executable then computes 1.5 and 27. Keeping the original expectation of 3 reports the observed bits 4609434218613702656 and exits with status 1. The second product reads its alpha from the allocation selected by `coefficient(scale)`. Lean replays both coefficient forms before emission. The pinned Lean emitter resolves the callee and its argument types in `emitFullApp`. [Scaled product module](../src/gemm-coefficients.ll) · [Physical coefficient regressions](../../tests/numerical_source.rs) · [Pinned call emission](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L755-L774)

The preview emits a direct storage call for each allocation, store, copy, expectation and drop in the two affine examples. Lean 4.35.0's `emitFullApp` resolves the callee and emits a typed call, and its conditional-branch builder takes an `i1` condition. Here each storage call returns `i32`, and `icmp eq` against zero selects the next call or the failure block. Both acquired-arena exits call `vstorage_delete` once. A null arena returns 1 before any storage call. The general Oracle theorem uses the status returned by each foreign call. The four width/carrier variants exercise the native implementation separately and preserve component bits through the identity copy. [Pinned call emission](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L755-L774) · [Storage theorems](../../lean/VastitasOracle/StorageProgram.lean) · [Native regressions](../../tests/numerical_realization.rs)

To add a sample, retain the complete public preview output in `llvm/src/`, register the source and its package in the replay runner, and register a closed theorem over that file in `Corpus.lean` under `checkedFiles`. Put commentary here so the file continues to match the bytes the theorem checks.


In the boxed-pairs fixture the accepted entry contains seven Core lets, a type
ascription and nine variable references. Both bodies of the assembled split
family also contain a scope and a variable reference. The MidIR builder gives
each bound name the initializer's existing SSA reference. Scope and a matching
ascription forward the child, so no instruction or stack slot is needed for
the binding itself. In Lean 4.35.0, `declareVars` visits each `FnBody.vdecl`
and `declareVar` allocates a prologue slot. On the ordinary declaration path
`emitBlock` calls `emitVDecl` on the initializer before visiting the rest of
the body. This comparison uses the pinned upstream source. The retained
4,157 bytes come from the Vastitas emitter.

The typed-forwarding regression replaces a direct parameter return with a
typed local in a singleton, a selected method and its fallback. Both versions
produce the same 1,237 bytes on the macOS target. All three functions retain
and return their input pointer. Reusing the first source revision with the
second source fails. On macOS arm64, LLVM 23.1.4 assembled and verified both
modules. Both objects linked with the boxed runtime and exited with status 42.
A Lean 4.35.0 control with the same typed local also returned 42. Its installed
compiler reported that bitcode output requires a build with `-DLLVM=ON`.
[Public regression](../../tests/llvm_preview.rs)
[Boxed pairs](../src/boxed-pairs.ll) · [Binding proofs](../../lean/VastitasOracle/BindingCoverage.lean) · [Lean variable declarations](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L979-L1007) · [Lean block emission](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L1153-L1164)

For the nested call `pick(delta(9, 4), delta(3, 1))`, both calls to `delta`
use the same function address. The selected method receives their SSA results
as `@vq_f1(ptr %v2, ptr %v5)`. Lean 4.35.0's `emitFullApp` resolves the
function ID, traverses its argument array in order, loads each slot and passes
those values to `LLVM.buildCall2`. For the retained 2,311 bytes, both the
Official and Fast boxed-program certificates verified the result 23. On macOS
arm64, LLVM 23.1.4 assembled, verified and compiled this file. With the final addition of 20, the
linked program returned 23. Swapping the two arguments or removing the applied
method returned 17 in each case. Lean/C controls produced the same three
results. The installed Lean compiler requires an LLVM-enabled build for the
upstream bitcode comparison. [Public call regression](../../tests/llvm_preview.rs) · [Call proofs](../../lean/VastitasOracle/StaticCallCoverage.lean) · [Pinned emitFullApp](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L755-L774)

The assembled conversion takes a borrowed heap `Nat`. Its shim retains that
reference before the consuming `lean_nat_to_int` call. The caller releases the
original after the selected method returns. The fallback accepts the same
argument and returns zero. LLVM 23.1.4 compiled both variants on macOS arm64.
A native probe compared each full integer before exit-status projection and
rejected a value larger by 256. Lean 4.35.0’s `emitInc` emits the reference
count increment requested by Lean IR. For the control `Int.ofNat` on a
borrowed parameter, Lean’s generated C called `lean_inc` immediately before
`lean_nat_to_int`; Clang 23.1.4 compiled the control and it returned status
43. [Checked conversion](../src/assembled-conversion.ll) · [Vastitas runtime shim](../runtime/exact.c) · [Lean reference-count emission](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L610-L624)

For every natural argument, the scoped conversion method returns the same
unbounded integer through its retained Core call and both checked MidIR
module invokers. When the operand is a branch, the Core-to-MidIR regression
selects a Nat block parameter before emitting the conversion. Both branch
outcomes pass. Validation rejects missing, mistyped, duplicated and
non-dominating operands. The public LLVM preview currently rejects this
branch-inside-conversion program. [Conversion proofs](../../lean/VastitasOracle/ConversionCoverage.lean) · [Branch regression](../../lean/VastitasOracle/MidIRRegression.lean)

Lean 4.35.0’s `emitJmp` checks join arity, stores incoming values in the
join parameter slots and emits a branch. For the control
`Int.ofNat (if pickHigh then high else low)` with borrowed operands, the
generated C retained and converted the chosen argument in each arm. Clang
23.1.4 at `-O1` emitted a pointer phi before the return. Its verified,
linked object selected the correct full integer in both directions for five
pairs, from 0 and 256 to 2¹⁰²⁴ + 43 and 2¹⁰²⁴ + 299. The installed Lean
toolchain rejected direct bitcode emission because it was built without
LLVM support. [Pinned join emission](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L1050-L1059)

In the four-file ordered-calls package, the dependency’s `same_base(0, 1)`
constrains an indexed family. Swapping these positions changes the function
revision while preserving both operands of `@vq_f1(ptr %v2, ptr %v5)` and the
complete module. Both inputs produced the same 2,311 bytes and a 2,256-byte
macOS arm64 object with LLVM 23.1.4. Both linked executables returned 23.
In a second comparison the dependency declared a package with a field
`Tag(7)`. Changing the unused field to `Tag(8)` changed the checked function
revision and preserved the same 2,311 bytes. The static LLVM 23.1.4 adapter
produced a 2,176-byte macOS arm64 object in each run. Both linked programs
returned 23. In a source that packs the witness, changing the index requires
the corresponding field type in the packing function. [Physical package checks](../../tests/indexed_definition_source.rs) · [Publication theorem](../../lean/VastitasOracle/BoxedCertificate.lean)

In Lean 4.35.0, `emitSimpleExternalCall` skips erased
parameters when building both the argument types and the call. As a control,
two Lean wrappers called the same external subtraction function with a static
`Type` argument of `Nat` or `Int` and two `UInt64` operands. Compiling the
generated C with Clang 23.1.4 produced `i64 @vast_family_sub(i64, i64)` in
both wrappers, with the operands in source order. This comparison covers
argument erasure and order. The Vastitas certificate checks the boxed integer
program against its own runtime ABI. [Certificate regression](../../experiments/compiler_validation/boxed_certificate/regression.py) · [Lean external call emission](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L656-L671)

On macOS arm64 the assembled negation calls `vastitas_int_neg_v1` with one borrowed
pointer. The caller releases its temporary after the method returns. Switching to the
identity method changes 1,389 bytes to 1,274 and invalidates the original function revision.
LLVM 23.1.4 and the generated Lean/C control returned −(2¹²⁸ + 43) and 2¹²⁸ + 43
for the two methods. The native probe checks the boxed integers before conversion to exit
statuses 213 and 43. In Lean 4.35.0, `emitSimpleExternalCall` constructs the external
function type and forwards its retained operands in order. The generated C for the exported
control calls `lean_int_neg` and then drops its owned argument. Clang 23.1.4, `llvm-as`,
`opt` and `llc` reproduced both results from that control.
[Lean control](../fixtures/AssembledNegationControl.lean) · [Pinned external call](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L656-L672)

The spectral action fixture reads the ordered entry of `J − 2I` for a two-dimensional
Jordan block. Its Lean/C executable returned 1, then 7 after editing the upper-right
coefficient, and 0 after interchanging the basis names. The boxed LLVM preview reports
`E_UNSUPPORTED` for this operation. On macOS arm64 the separate Lean 4.35.0
matrix control produced the same three results after C emission, Clang 23.1.4 IR
generation, assembly, verification, object emission and linking. The control's generated
C selects the row and column using `lean_ctor_get`. Lean's `emitProj` passes the field
index to this same accessor. [Vastitas source](../../tests/fixtures/spectral-action-source.vast)
· [Lean control](../fixtures/SpectralActionControl.lean)
· [Pinned projection emission](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L795-L811)

The selected-projection module calls the versioned boxed pair shim and its first- or second-field entry.
The linked method proof covers both integer sorts and every argument value.
Removing the assembly's `apply` selects the sibling that reads field zero.
[Checked pair method](../fixtures/SelectedProjection.vast) · [Linked projection theorem](../../lean/VastitasOracle/PairCoverage.lean)

The physical primitive comparison covers a used coordinate as well. In the
frames package, `frame_component(Coords, 0)` and `frame_component(Coords, 1)`
selected 7 and 19 from the same frame vector on the Lean/C native path.
The public LLVM preview returned `E_UNSUPPORTED` for this frame program.
Lean 4.35.0's `emitProj` passes the static field index to `lean_ctor_get`.
In a separate two-field `Nat × Nat` control, Lean-generated C used indices
0 and 1. Clang 23.1.4 at `-O1` lowered the payload reads to byte offsets 8
and 16 on macOS arm64. The assembled and verified module linked and returned
the same two coordinates. The control compares field selection. Frame layout
and the mathematical interpretation of its coordinates belong to the Vastitas
checker. [Lean field projection control](../fixtures/SelectedProjectionControl.lean) · [Physical primitive regressions](../../tests/indexed_definition_source.rs) · [Pinned Lean projection emission](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L796-L810)

For the first frame vector `(1, s)` and a Gram matrix with rows `(g, 1)` and
`(1, 1)`, its first Gram entry is `(g + s) + s * (1 + s)`. The Vastitas
Lean/C executable returned 2, 3 and 5 for `(g, s) = (2, 0), (3, 0), (2, 1)`.
These runs change the physical metric entry or the physical frame column.
A separate Lean 4.35.0 function on two `Int` parameters generated three calls
to `lean_int_add` and one to `lean_int_mul`. On macOS arm64, Clang 23.1.4
emitted the LLVM module from its generated C. LLVM assembled and verified
that module, and the linked control returned the same three results. In the
Lean emitter, standard external calls construct a function type from retained
arguments in order. The Vastitas LLVM preview reports `E_UNSUPPORTED` for the
used frame operation. [Native frame regression](../../tests/indexed_definition_source.rs) · [Lean external call emission](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L656-L682)

The two-object isomorphism module passes the two arrows to the composition
functions in opposite orders. Its nested conditions join the exit values 42,
7 and 9 using two LLVM phi nodes. Lean 4.35.0's `emitJmp` stores join
arguments in slots before branching, and `emitJDecl` allocates variables for
the join body. The corpus theorem covers every byte of the explicit-phi
module. On macOS arm64, LLVM 23.1.4 emitted a 1,976-byte object. The linked object, the public native preview, the Lean/C build and a Lean control composing explicit endpoint pairs all returned 42. The pinned upstream executable reported no LLVM feature. [Lean join arguments](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L1050-L1060) · [Lean join declarations](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L1130-L1144)


The S3 opposite fixture constructs its expected LLVM model by composing the
three images of each permutation. It derives the inverse by locating each
image. Both switches check unsigned bounds before flattening their two
arguments. The entry passes the branch results to one explicit phi. An
[independent Lean reference](../../experiments/compiler_validation/llvm/OppositeComparison.lean) checks the inversion law for all 36 pairs and returns 42.
Lean 4.35.0 emits `switch` for tagged cases and stores join arguments on a
jump. Its pinned binary reports no LLVM backend feature.
[Lean tagged cases](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L1090-L1137) · [Lean join arguments](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L1050-L1060)

For a checked finite entry, Lean resolves the declarations from the supplied
`.vast` files, including unused tables. Their owners, tags, rows and instance
fields agree in order with the finite entries in Core and both MidIR phases.
The theorem follows the same execution MidIR to the LLVM model and its complete
printed bytes. [Source and Core correspondence](../../lean/VastitasOracle/ResourceSource.lean) · [Finite entry and LLVM bytes](../../lean/VastitasOracle/FiniteProgram.lean)

Two valid affine isomorphisms can exchange their forward and inverse maps.
A Cartesian square can also select a second declaration of the same inverse
map. With an entry returning 10, all three source variants reproduce the 374
bytes of the folded-arithmetic module. Mixing the physical source and decoded
witness from different variants fails before emission. The witnesses are
checked during elaboration and leave no calls in this closed entry. In Lean
4.35.0, `emitMainFn` calls the program and unboxes its exit status.
[LLVM file](../src/folded-arithmetic.ll) · [Public source regression](../../tests/affine_geometry.rs) · [Lean main emission](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L1577-L1590)

An edition-2026 package declaring an exact complex affine plane and returning
the integer 42 emits the same complete module as the constant entry alone.
On the retained macOS target it has 374 bytes and ends in `ret i32 u0x2A`.
The declarations select a mathematical model during checking. This example
exercises their erasure from a closed entry. Lean 4.35.0's hosted main obtains
the result of a call and unboxes its status. [Public regression](../../tests/exact_affine_models.rs)
· [Lean's main function](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L1583)


### A conditional that returns a parameter

The assembled `choose(flag, left, right)` passes either the second or third parameter
to a single integer block argument. The optimization and execution MidIR modules each
contain four blocks for this method. The joined reference depends on the incoming edge.
Exchanging the two integer references still satisfies the SSA type checker and changes
the result. The Lean proof preserves their positions in the original scoped and ascribed
Core arms. The public replay checks the exact called target and revision and compares
the full Core integer with both MidIR observations. [Source](../fixtures/ConditionalMethod.vast) · [Public replay](../fixtures/ConditionalMethodReplay.lean)

With the contribution applied, the two branches returned 2¹²⁸ + 43 and −19. The default
method returned −19 on the same true input. Their Lean/C native exit statuses on macOS
arm64 were 43, 237 and 237. The macOS arm64 objects generated from the boxed Vastitas LLVM modules returned
the same three full integers. In each conditional the selected edge carries the
borrowed integer to the pointer `phi` and transfers its ownership to the join. In the pinned Lean distribution, `lean --features` returned `[]`
and `lean -b` reported that LLVM support was disabled. For the independent control,
Clang 23.1.4 compiled the generated Lean C at `-O0`. Its LLVM IR branches on an
8-bit Boolean, releases the unselected boxed integer and returns the selected pointer
through a stack slot. Upstream `emitJmp` checks the argument count, stores each argument
in the join parameter's slot and branches to the join. [Lean control](../fixtures/ConditionalMethodControl.lean) · [Pinned jump emission](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L1050-L1060)


### Comparisons on integer parameters

The assembled `before(x, y)` compares its two parameters in their written
order. Removing its contribution makes the default method compare them in
reverse order. The public replay covers six comparisons for each of Nat and
Int, including equal arguments and distinct integers with identical low bytes.
It checks the selected callee, SSA operand order, common function revision
and complete Core and MidIR observations. The macOS Lean/C executables returned
42 and 7 for the two selections with either numeric type. The hosted LLVM corpus example retains both methods, calls the selected
comparison and branches on the returned 32-bit Boolean. The native macOS
qualification observed the full integers 42 and 7 for the two selections.
[Source](../fixtures/ComparisonMethod.vast) · [Public replay](../fixtures/ComparisonMethodReplay.lean)

For a direct call with arguments, Lean 4.35.0's `emitFullApp` resolves the
IR function ID, loads the arguments in order and passes the function type and
values to `LLVM.buildCall2`. Vastitas prints a local symbol such as `@vq_f0`.
The proof reads each caller's direct calls from its parsed LLVM instructions,
then recovers the original Core symbols and their occurrence counts through
both SSA phases. For a dispatch target it also identifies the source caller
and the method selected by assembly at the published revision.
[Lean direct-call emitter](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L755-L773) · [Vastitas call correspondence](../../lean/VastitasOracle/FlowCertificate.lean)

In the Boolean comparison fixture, both parameters use the boxed program's
scalar Boolean ABI. The printer compares two `i32` values with `icmp eq` or
`icmp ne`, then widens the `i1` result to `i32` with `zext`. The parser
checks that the extension consumes that comparison in the same block.
The source calls the selected method for all four ordered input pairs.
Their weights are 1, 2, 4 and 8, so equality contributes 9 and inequality 6
to the same unbounded integer. Lean 4.35.0 uses an `i8` Boolean ABI in
`buildLeanBoolTrue?` and compares it with zero to obtain a branch condition.
The native regression compares the two full integer results with a compiled
Lean control. [Lean Boolean conversion](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L485-L488) · [Lean control](../fixtures/ComparisonMethodControl.lean) · [Word comparison proof](../../lean/VastitasOracle/ExactFlow.lean)

On macOS arm64, Lean 4.35.0 and nanoda 0.4.19 checked the same export for
the selected comparison. It covers two physical files, three retained
functions, the integer result 42 and all 2,382 LLVM bytes. Lean's external
kernel replay took 4.96 seconds and peaked at 551 MiB RSS. Nanoda checked
5,936 declarations in 11.24 seconds and peaked at 3,378 MiB RSS. These
measurements cover the verifier processes. Certificate generation and native
execution have separate costs. [Certificate replay](../../experiments/compiler_validation/boxed_certificate/README.md)

Lean 4.35.0's external-call emitter builds the function type and call from
the ordered, retained parameters. In the generated C control, greater-than
reverses the operands of `lean_nat_dec_lt` or `lean_int_dec_lt`.
Greater-than-or-equal similarly reverses the less-than-or-equal call.
On macOS arm64, Clang 23.1.4 emitted two pointer operands and an 8-bit
Boolean result. The native control passed 24 cases for each type, with
operands up to 1,025 bits. Direct upstream bitcode emission is disabled in the
pinned Lean installation. The native qualification runs these 48 generated-C
comparisons on both hosts. Its separate upstream emission record attempts
source-to-bitcode and disassembly when the installed Lean exposes LLVM.
[Native qualification](../check_exact_native.py) · [Upstream qualification](../../experiments/compiler_validation/llvm/run.py) · [Lean comparison control](../fixtures/ComparisonMethodControl.lean) · [Pinned external-call emission](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/IR/EmitLLVM.lean#L656-L673)


For a single exported straight-line function, the Vastitas LLVM ABI passes
each integer as a borrowed pointer. The comparison shim calls the pinned
Lean runtime and widens its Boolean to `uint32_t`. Clang 23.1.4 emitted a
`zeroext` return attribute for a C `uint8_t` on both macOS arm64 and Linux
x86-64. A C `uint32_t` has the plain LLVM return type `i32` on both targets.
For `a - 256 <= b`, the library releases the subtraction result and the
literal after the comparison. The C caller receives 0 or 1 directly. On macOS, LLVM 23.1.4 assembled and verified the 897-byte Linux-targeted variant and emitted a 1,344-byte x86-64 ELF object.
The qualification compiles all twelve Nat/Int predicates and checks the
two input reference counts, including cases with aliased heap integers.
[Complete LLVM file](../src/integer-predicate.ll) · [Caller and ownership probe](../fixtures/IntegerPredicateProbe.c)
