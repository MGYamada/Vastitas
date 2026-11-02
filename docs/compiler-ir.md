# Compiler IR v1: Lean IR → Vastitas MidIR → LLVM IR

**Normative specification target:** Vastitas **v0.1.0**, tracked by [#417](https://github.com/MGYamada/Vastitas/issues/417). This document fixes the v1 representation contract, lowering obligations, LLVM backend choice and release acceptance criteria. **It describes a required implementation and proof target, not a claim that the current compiler already implements or proves it.** The existing Rust → Lean-checked Core → Lean/C native path is the current baseline until the new path passes its gates.

## 1. Architecture and trust boundary

~~~text
.vast source / package inputs
    │
    ▼
Rust frontend and wire encoder             [UNTRUSTED]
    │ candidate only
    ▼
Lean source/authority/type/resource checks  [ACCEPTANCE]
    │
    ▼
Lean IR: accepted Vastitas Semantic Core    [AUTHORITATIVE INPUT]
    │ verified lowering
    ▼
Vastitas MidIR v1, optimization phase       [CHECKED CANDIDATE]
    │ verified optimization / phase change
    ▼
Vastitas MidIR v1, execution phase          [CHECKED CANDIDATE]
    │ verified LLVM emission
    ▼
exact emitted LLVM IR (.ll)                 [VERIFIED OUTPUT ARTIFACT]
    │
    ▼
LLVM optimizer/code generator, assembler,
linker and external runtime                 [UNTRUSTED HOST BOUNDARY]
    │
    ▼
native executable
~~~

- **Lean IR** means the actual, independently accepted, typed Vastitas Semantic Core represented in Lean, tied to the exact source/dependency snapshot and accepted `fn` family/method. It does **not** mean Lean 4's compiler LCNF or a claim about the verified correctness of the Lean-to-C compiler.
- **Vastitas MidIR v1** is **one proprietary, Lean-defined, phase-indexed IR**, not two independent semantic authorities. Its `optimization` phase exposes SSA/control, mathematical/effect/ownership facts and lawful rewrites (#418); its `execution` phase exposes actual memory, control, scheduling, numerical and ABI choices (#420). The Semantic Core contract is #419.
- **LLVM IR is the canonical v0.1.0 backend target.** The exact LLVM module emitted by Vastitas is the endpoint of the certified compiler-transparency claim. LLVM `opt`/`llc`/Clang/assembler/linker and their native results stay **outside the trust boundary**, even when they are used to produce a binary.
- **Rust is outside the trust boundary.** Frontend ASTs, wire input, cached MidIR, LLVM text, hash values and diagnostic receipts are untrusted candidates. They never construct accepted Core, valid proof evidence or owner/borrow rights. The current official Lean kernel and its checked theorems are the only proof authority, with the independent Universe Charter defining the admitted fragment (#184/#229/#350).
- Do not silently fall back to the current Lean/C backend in a build advertised as v0.1.0 certified LLVM compilation. Preserve historical/differential paths with explicit labeling until transition; the v0.2.0 Lean-native frontend migration (#152) is a separate later change.

The trust claim does **not** include the physical correctness of LLVM-generated machine code, a native runtime/BLAS implementation or a foreign ABI merely from verified `.ll` emission. External runtime calls require explicit interface contracts and labeled assumptions. A future native-code refinement theorem would require additional work.

## 2. Frozen v1 MidIR data model

The source language and public source-wire protocol are **not** serialized MidIR. A MidIR dump is an internal, versioned debug/transport artifact, never an `AcceptedProgram` or public stable ABI. The **Lean typed constructors and checked well-formedness predicates are normative**; text/binary encodings must round-trip into candidate values and be revalidated.

~~~text
ModuleV1 {
  schema_version = 1,
  phase: optimization | execution,
  producer_revision, charter_revision, admission_profile,
  source_snapshot, dependency_revisions,
  target_triple, data_layout, abi_profile, numeric_profile,
  functions: [FunctionV1], provenance_refs
}

FunctionV1 {
  package_id, defining_module_id, function_id,
  selected_method_id, assembly_revision, specialization_key,
  signature, effect_profile, entry_block, blocks: [BlockV1]
}

BlockV1 {
  block_id, params: [(value_id, runtime_type)],
  ops: [OpV1], terminator: TerminatorV1
}

OpV1 {
  op_id, kind, typed_operands, typed_results,
  type_and_nominal_refs, control_and_effect_dependencies,
  ownership_and_loan_state, shape_stride_layout,
  numeric_order_rounding_flags, origin_refs, obligation_refs
}

TerminatorV1 =
  branch(target, typed_args)
  | cond_branch(condition, then_target, then_args, else_target, else_args)
  | return(typed_values)
  | fail(typed_error_and_cleanup)
  | unreachable(proved_unreachable_ref)
~~~

**Required invariants and instruction families:**

1. **Identity and typing.** All symbols and references resolve within one pinned snapshot; `PackageId/ModuleId/FunctionId`, selected method/body, grant/assembly revision, nominal type/object endpoints and finite specialization are immutable under lowering. A family value is not a monomorphic runtime function pointer without checked specialization. Every value, branch argument, call and result is well-typed; generative identity cannot be reconstructed from equal dimensions/layouts.
2. **SSA and effects.** Immutable computational values use typed SSA/block parameters. Control-flow joins, loops and failure edges must preserve explicit effect order, move state, borrow permissions, initialization state, allocation generation and cleanup obligations. SSA alone conveys no alias or ownership permission.
3. **V1 operation groups.** The finite v1 registry must define constructors, typing rules, operational semantics and lowering obligations for: pure constants/arithmetic/comparisons/casts; aggregates and nominal projection/packing; calls and control-flow; ownership, borrowing, allocation, load/store, bounds checks and cleanup; numerical operations and externally contracted calls. A phase may retain a higher-level operation (e.g. tensor contraction/GEMM) only with a declared denotation and a checked lowering before LLVM emission. New/unknown operation tags are rejected; an arbitrary extension may not silently become a v1 operation.
4. **Optimization phase.** Carry source-selected algorithms, exact arithmetic laws and numerical realization, effects/AD eligibility, shape/stride and disjointness evidence while needed. Transformations require independently checked legality before heuristic profitability; no invented differentiability, hidden algorithm substitution, unchecked reassociation, or manufactured proof status (#389/#415).
5. **Execution phase.** Specify stack/heap/region operations, physical layout/alignment/strides, guards, initialization, moves, cleanup on every path, loops/SIMD/scheduling, calling convention, target data layout, exact external interface and floating flags/order. Erasing a mathematical or ownership attribute requires a corresponding checked preservation argument and compiler-side evidence link.
6. **Canonicalization.** Deterministic declaration/block/value ordering and alpha-renaming, bounded decoding, checked CFG/dominance/block arguments, explicit symbol tables and versioned text/machine formats. No timestamp or absolute path participates in semantic identity. Reject malformed, stale, forged, unknown-version or inconsistent MidIR as untrusted data. A hash is an identifier, **not** a proof.
7. **Version rule.** `schema_version=1` fixes these mandatory fields, phase judgments, validity/semantic conditions and rejection behavior for v0.1.0. Concrete opcode registration is closed for each pinned implementation revision; additions/change of semantics require an explicit version/registry revision plus replay of relevant obligations. Optimizer pass order and physical backend implementation are not a public ABI.

## 3. Lean-checked lowering and exact LLVM output

Let `C` be the **actual accepted** Lean Core, `Mₒ`/`Mₑ` the two MidIR phases, and `L` the **exact emitted LLVM IR file**. For an admitted source/target/environment `E`, the certified build must establish, for its **real artifacts**, the composed chain:

~~~text
Accepted(C, E)
  ∧ Verify(C → Mₒ, E)
  ∧ Verify(Mₒ → Mₑ, E)
  ∧ Verify(Mₑ → L, E)
  ⇒ ObsLLVM(L, E) refines ObsCore(C, E)
~~~

Here `Verify` means a Lean-checked pass-correctness theorem **instantiated for the actual pass and its exact input/output**, or a Lean translation validator whose soundness theorem the official Lean kernel checks. A pass receipt, checksum, `proved` label, executable test or external SMT/LLVM analysis **alone** is not `Verify`. Compose genuine theorem evidence through #229's existing authority/obligation ledger; do not add a parallel proof oracle. No unsupported step may be classified as certified.

The observation/refinement relation must **explicitly** specify the supported program outputs, return/failure/error behavior, divergence (where modeled), observable effects and order, allocation/ownership safety, exact integer behavior and declared floating semantics (operation order, rounding, flags, traps and allowed nondeterminism). For nondeterministic allowed behaviors, use an explicitly stated trace-refinement relation; do not assert byte-equality of all possible executions. Conditional foreign-runtime/ABI assumptions must be visible and never be mislabeled a proof of those components.

The finite supported LLVM IR subset needs a Lean-defined semantic/typing correspondence, including target layout and all emitted instruction/attribute semantics. In particular:

- No unsupported `undef`/`poison`/`freeze` use, undefined behavior, unwarranted `nuw`/`nsw`/`inbounds`/`nonnull`/alias attributes or unrestricted `fast-math`; show each precondition or do not emit it. Bounds/overflow guards and a valid failure path may be required.
- Preserve arbitrary-precision Nat/Int where admitted (do not silently narrow), nominal and region-based safety even after metadata erasure, function/ABI identity, and explicit external calls.
- Verify **the actual emitted `.ll` bytes** by a bounded independent Lean-side parse/check or equivalent proven emitter-plus-round-trip correspondence, bound to compiler/version/target/options. Merely proving correctness of a pre-printer AST or naming a digest does not establish what LLVM receives.
- The LLVM compiler may parse, optimize and lower the checked `.ll` to native code, but none of these external transformations inherits the Lean-to-LLVM-IR theorem. If an external `opt` stage produces another IR file, that transformed file is unverified unless separately checked.

The **certified build must fail closed before LLVM invocation** if any applicable translation step, emitted LLVM construct or exact-output correspondence lacks discharged evidence. `vastitas check` may still report independently accepted source without claiming a certified executable. Unverified experimental lowering, if offered, must be explicit and outside certified `build`.

## 4. Transparency records, caches and visibility

For each actual pass/decision, emit #414's versioned provenance receipt with: accepted-Core identity and source/selected-method revision; actual input/output MidIR artifact identities; transformation and target; applied/skipped/failed reason; exact semantic obligation and kernel-checked evidence reference; and final `.ll` bytes identity. Build a deterministic normalized DAG of **actual** transitions. `proved / conditional / unverified / unknown` are reporting states, not acceptance authority. For a **certified** Core→LLVM chain every internal required obligation must be discharged; external host/runtime assumptions remain labeled outside that theorem.

`--explain=text|json` and IR inspection (#415/#416) observe the receipts without influencing acceptance, code generation or proof status. Cache behavior (#339) must independently reconstruct current accepted Core and rerun all v0.2.0 Vastitas-owned IR/emission passes; only a protected, whole-program external LLVM-toolchain result may be reused under its separate authorization/key. Its input key is the **exact LLVM `.ll` and associated emitted files** plus pinned external toolchain/environment/ABI inputs, **not** the historical `Main.lean` emitter. Cache bytes never prove a theorem.

## 5. v0.1.0 release acceptance

The **first implementation scope** is every executable construct admitted by the declared v0.1.0 finite profile (including #462's unified finite `fn` model when implemented); it does **not** move #405's generic `Vec<T>`/loop/ADT or #408's general type/const specialization from v0.2.0 into v0.1.0. Later language features must extend this same verified route and registry.

- [ ] **Spec and representations:** implement the phase-indexed MidIR v1 Lean constructors, validators, versioned serialization, deterministic printer/parser and rejection of forged/stale/ill-typed/illegal-resource direct-IR candidates.
- [ ] **Real pipeline:** connect accepted `.vast` Core → optimization MidIR → execution MidIR → emitted LLVM `.ll` on the actual `check/build` path; identify the last emitted LLVM bytes, target triple, data layout, ABI, toolchain revision and options. LLVM is the production v0.1.0 native backend; old Lean/C remains an explicitly marked legacy/differential path only.
- [ ] **Formal transparency:** discharge every internal pass and LLVM emission refinement obligation for the finite admitted v0.1.0 profile, composing checked evidence to the exact emitted LLVM text. No `unknown`, `conditional` or `unverified` **internal** preservation gap may pass certified `build`. Keep external host/FFI assumptions disclosed.
- [ ] **Adversarial tests:** Rust/source-wire spoofing; altered MidIR identity, owner, method winner, specialization, loans, CFG, proofs; tampered LLVM bytes, ABI, attributes, alias claims, numeric policy and missing evidence all fail closed. Check preservation of pure values, failures/cleanup and at least one resource/numerical path that is actually supported.
- [ ] **User-visible boundary:** source `check` without native steps, certified and rejected `build`, opt-in accurate trace, no invented pass executions or proof claims, and explicit separation from host LLVM/assembler/linker correctness. Linux/macOS end-to-end native tests are additional evidence, not theorem substitutes.
- [ ] **Quality measurements:** compare actual LLVM-backed execution against matched C/C++ for time, allocations/copies and peak memory (#222) without treating use of LLVM or a benchmark as a correctness or performance theorem.

**Dependencies and scope:** #152 (later Lean-native frontend), #184/#192 (constitutional CS/MS/CF), #229 (authority/obligation ledger), #350 (Charter), #339 (v0.2.0 cache), #389/#405 (algorithm/Core), #414–#416 (diagnostics), #418/#419/#420 (layer contracts), #462 (v0.1.0 finite `fn`). The official Lean kernel remains the only proof authority; no new Domain Checker, second semantic Core, user-facing `unsafe`, stable public IR ABI, completed proof, native binary guarantee, or measured C/C++ parity is implied by this specification.
