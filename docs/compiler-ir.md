# Compiler IR v1: accepted Lean Core → Vastitas MidIR → LLVM IR

## Interim specification precedence (2026-11-13)

Until the successor specification tracked by [#749](https://github.com/MGYamada/Vastitas/issues/749) is on `main`, PR #480 remains the baseline IR specification **only where it is consistent with the resolved decisions 1, 2, 3, 5, 7 and 8 of #749 (2026-11-13)**. Those resolutions take precedence over conflicting wording in PR #480, including its specification file and earlier summary. In particular, the v0.1.0 independent semantics live in their own `VastitasOracle` namespace; numerical execution uses the declared `NativeFast` adapter/foreign-call contract, emits no LLVM floating-point instructions, and rejects strict or LLVM-default floating profiles. Earlier FP routes in PR #480 are not v0.1.0 admission requirements. The other resolved runtime, ownership, carrier and GEMM choices retain their exact scope in #749.

This is a precedence clarification, not a new design decision, implementation claim or completed proof. Decisions 4 and 6 and both feasibility spikes remain unresolved/blocking as recorded in #749; this paragraph neither selects an option nor waives their acceptance obligations. The planned successor under `docs/spec/` remains required, with Planned claims and evidence-scoped status transitions. PR #480 is not thereby made merge-ready and is to be closed only when that successor is on `main`.

---

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
Accepted Lean Core: Vastitas Semantic Core [AUTHORITATIVE INPUT]
    │ verified lowering
    ▼
Vastitas MidIR v1, optimization phase       [CHECKED CANDIDATE]
    │ verified optimization / phase change
    ▼
Vastitas MidIR v1, execution phase          [CHECKED CANDIDATE]
    │ verified LLVM emission
    ▼
exact emitted LLVM IR (.ll)                 [MODE-AUDITED OUTPUT ARTIFACT]
    │
    ▼
Rust llvm-sys adapter / linked libLLVM
and linker/runtime                          [UNTRUSTED HOST BOUNDARY]
    │
    ▼
native executable
~~~

- **Accepted Lean Core** means the actual, independently accepted, typed Vastitas Semantic Core represented in Lean, tied to the exact source/dependency snapshot and accepted `fn` family/method. It is **not** Lean 4's LCNF/compiler IR or a claim that Lean's native compiler is verified.
- **Vastitas MidIR v1** is **one proprietary, Lean-defined, phase-indexed IR**, not two independent semantic authorities. Its `optimization` phase exposes SSA/control, mathematical/effect/ownership facts and lawful rewrites (#418); its `execution` phase exposes actual memory, control, scheduling, numerical and ABI choices (#420). The Semantic Core contract is #419.
- **LLVM IR is the canonical v0.1.0 backend target.** The exact LLVM module emitted by Vastitas is the endpoint of the Official-mode kernel-checked compiler-transparency claim, and the default Fast-mode nanoda-audited artifact. In-process `libLLVM` through Cargo/`llvm-sys`, the native linker and their generated results stay **outside the trust boundary**, even when linked into the compiler; external `llvm-as`/`opt`/`llc` are optional diagnostic tools.
- **Rust is outside the trust boundary.** The Rust frontend and the isolated `llvm-sys` backend adapter are untrusted. Frontend ASTs, wire input, cached MidIR, C-API built/parsed LLVM modules, LLVM text, hash values and diagnostic receipts are untrusted candidates. They never construct accepted Core, valid proof evidence or owner/borrow rights. The official Lean kernel and its checked theorems are the only **formal/constitutional** proof authority; pinned toolchain-shipped `nanoda_bin`, run out of process, may be operationally trusted as the default Fast proof auditor, with the independent Universe Charter defining the admitted fragment (#184/#229/#350).
- Do not silently fall back to the current Lean/C backend in a build advertised as an Official-checked v0.1.0 LLVM compilation. Preserve historical/differential paths with explicit labeling until transition; the v0.2.0 Lean-native frontend migration (#152) is a separate later change.

The trust claim does **not** include the physical correctness of LLVM-generated machine code, a native runtime/BLAS implementation or a foreign ABI merely from verified `.ll` emission. External runtime calls require explicit interface contracts and labeled assumptions. A future native-code refinement theorem would require additional work.

### Cargo-linked LLVM implementation and release policy (normative v0.1.0)

- **Standard backend:** The normal Cargo-built Vastitas compiler uses a thin, isolated **Rust/`llvm-sys` adapter** to pass checked LLVM IR through the LLVM C API for **in-process** optimization and target-machine/object generation. A platform linker remains external; spawning `llvm-as`/`opt`/`llc` is not the required production backend. These commands may be used for independent diagnostics. Neither Rust nor libLLVM may become source/IR semantic acceptance or proof authority.
- **Exact versioned dependency:** Fix `llvm-sys = "=231.0.1"` for the LLVM **23.1** C ABI, with LLVM **23.1.4** as the first exact native library/build candidate to qualify on Linux/macOS. `llvm-sys` is C-API **bindings, not bundled native LLVM**: Cargo full-source builds need a compatible `llvm-config` and LLVM development libraries supplied from an explicit pinned distribution/build (e.g. `LLVM_SYS_231_PREFIX`). Missing, mismatched or unsupported libraries cause a clear failure, and the pin is not called tested/supported until CI establishes it. Keep the Cargo lockfile and native-library provenance; no arbitrary automatic LLVM downloads inside Cargo build scripts.
- **User distribution:** Prefer **static linkage of libLLVM** into supported release binaries. A prebuilt `vastitas` then needs neither separately installed LLVM nor Cargo/Rust to run; this does not promise fully static linkage of all system libraries. Full compiler **source** builds require the pinned Cargo/Rust+LLVM toolchain. A separate Lean-only source `check`/proof profile may omit this backend and must not claim native `build`.
- **Verified C-API boundary:** Lean authorizes the **complete exact final `.ll` bytes**. Recompare the final on-disk file and pass those same bytes unchanged to libLLVM's parser **before** any optimizer/target-machine step. LLVM's IR verifier is diagnostic only. If a Rust/C-API builder constructs a module instead, reserialize its actual pre-optimization module and independently validate exact correspondence to the Lean-authorized module/bytes; a builder cannot insert an unproved attribute/flag, edit the mode-checked input or silently create a second accepted IR. Parser/handoff behavior remains an explicit external premise.
- **Reproducibility:** Each release/build record binds `llvm-sys` crate/lock, libLLVM full version/build/link mode/library identity, LLVM pass and target-machine options, ABI/data layout/triple, runtime/linker, exact validated `.ll` bytes and all associated inputs. LLVM upgrades or other FFI/link changes require compatibility, Linux/macOS native tests, parser-differential and adversarial-corruption checks. Proof still ends at LLVM IR, never native code.
- **v0.2.0 migration:** #152 migrates the source frontend, semantic acceptance and primary CLI to Lean **while retaining this untrusted Rust/`llvm-sys` codegen library**. Full source-native builds may still require Cargo, whereas packaged binaries do not; the pinned toolchain-shipped `nanoda_bin` Fast verifier, run out of process, is required for default Fast, while the standalone `audit-lean` diagnostic remains optional (#282).


### Compiler verification modes and Lean distribution (normative v0.1.0)

The public CLI offers exactly **two** verification modes: `vastitas check/build --mode=fast|official`. **`fast` is the default; `official` is opt-in.** These names identify the verification *implementation*, not a claim that nanoda is incorrect. Constitutional CI is a separate governance/proof layer, **not a third compiler mode**.

| Boundary | Verifier, obligations, receipt |
| --- | --- |
| **Fast** (default) | Pinned toolchain-shipped `nanoda_bin` (nanoda 0.4.19 for Lean 4.35.0), run out of process, operationally audits Lean proof exports **bound to the current source/Charter/environment, exact accepted Core, MidIR and complete emitted LLVM `.ll` bytes**. Successful audit may permit Fast compilation without current-run official-kernel replay. Record `verification_mode=fast`, `verifier=nanoda`, `official_kernel_checked=false`. This is a declared implementation trust premise, not an Official/Constitutional proof. |
| **Official** (explicit) | Pinned **official Lean kernel** independently checks the actual source/IR/LLVM emission evidence, proof statements, authenticated axiom/environment closure and cross-function/module composition for the *current* build, including native cache hits. Record `verification_mode=official`, `verifier=lean-official`, and only on success `official_kernel_checked=true`. Neither Rust nor nanoda can approve this mode. |
| **Constitutional CI** | Official Lean kernel alone checks general stage-validation soundness, Universe Charter, #192 CS/MS/CF under #184 global applicability/composition (#191 owns only the stream-specific MS corollary) and proof/release claims. Nanoda/Rust results are candidate data or diagnostics, never constitutional proof authority. |

Both user modes retain the **same language semantics and Lean-owned structural/domain/ownership validation**, admitted profile, canonical stage/LLVM output, identical byte handoff and fail-closed rejection. Nanoda is a Lean **proof-export checker**, not a validator of arbitrary LLVM bytes by itself: the input-to-proof-to-complete-IR mapping and standard-axiom environment must be authenticated before Fast may actually gate `check/build` (#282/#159/#184). A standalone `audit-lean` success or an old cache proof flag is never sufficient. Never silently switch modes; never label Fast output Official. Test cross-mode agreement on valid and adversarial cases rather than assuming it without evidence.

**Distribution:** pin the exact official Lean 4.35.0 toolchain and its kernel-based `leanchecker --from-export` / `lake check --from-export` path, including its toolchain-shipped `nanoda_bin` 0.4.19, run out of process, alongside the LLVM pins. Lean 4.35.0 officially distributes the kernel and nanoda verifiers already; do not reimplement the kernel. For Linux/macOS prebuilt releases, prefer bundling the toolchain-shipped `nanoda_bin` executable for Fast and **an isolated, matching official checker/runtime/standard-environment sidecar** for Official (no user installation of elan, Cargo, LLVM, or build-time network fetching). Validate minimal subset packaging by real loader/ABI/export/authenticity tests; fall back to the necessary official toolchain files if minimization is not qualified. Source builds may use the exactly pinned official toolchain. Record component hashes and licenses; a missing/mismatched Official component is an explicit error, not a Fast fallback. This packaging is a **target requiring platform qualification**, not a claim that binaries are currently shipped.

**Implementation and coverage boundary (#282/#539):** the delivered out-of-process `audit-lean` diagnostic and verifier identity pin do not establish current-artifact Fast/Official compiler integration or complete export/audit coverage. Record unsupported declaration/export forms in the versioned Fast trust-assumption/coverage ledger; reject unsupported, truncated, ambiguous or unbound evidence without silent fallback. No separately linked Cargo `nanoda_lib` dependency is required by this contract.

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
  numeric_order_rounding_flags, target_promise_slots,
  origin_refs, obligation_refs
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
5. **Execution phase.** Specify stack/heap/region operations, physical layout/alignment/strides, guards, initialization, moves, cleanup on every path, loops/SIMD/scheduling, calling convention, target data layout, exact external interface and floating flags/order. The execution denotation must **never inspect proof-only metadata** after its obligations have been discharged; dropping *only those inert fields* is definitionally semantics-preserving. Consuming ownership facts, changing layout/control/cleanup, or changing a runtime-relevant attribute still requires checked refinement and evidence. Never erase an ownership or proof fact before every relying pass has consumed it.
6. **LLVM promise slots.** Typed `target_promise_slots` reserve (but do not authorize) future LLVM overflow, range, alias, capture, memory-effect and floating-point promises. The v0.1.0 safe baseline emits none of the poison/UB-generating promises until the admitted subset models each one and a kernel-checked obligation establishes its validity on every admitted Core execution. An unproved or unknown promise must fail either `fast` or `official` `build`; extra promises require an explicit registry/profile revision.
7. **Canonicalization.** Deterministic declaration/block/value ordering and alpha-renaming, bounded decoding, checked CFG/dominance/block arguments, explicit symbol tables and versioned text/machine formats. No timestamp or absolute path participates in semantic identity. Reject malformed, stale, forged, unknown-version or inconsistent MidIR as untrusted data. A hash is an identifier, **not** a proof.
8. **Version rule.** `schema_version=1` fixes these mandatory fields, phase judgments, validity/semantic conditions and rejection behavior for v0.1.0. Concrete opcode registration is closed for each pinned implementation revision; additions/change of semantics require an explicit version/registry revision plus replay of relevant obligations. Optimizer pass order and physical backend implementation are not a public ABI.


## 3. Lean-checked lowering and exact LLVM output

Let `C` be the **actual accepted** Lean Core, `Mₒ`/`Mₑ` the two MidIR phases, and `L` the **exact emitted LLVM IR file**. For an admitted source/target/environment `E`, an `official` build must establish by the official kernel (and a `fast` build must audit with bound nanoda evidence), for its **real artifacts**, the composed chain:

~~~text
Accepted(C, E)
  ∧ Verify(C → Mₒ, E)
  ∧ Verify(Mₒ → Mₑ, E)
  ∧ Verify(Mₑ → L, E)
  ⇒ ObsLLVM(L, E) refines ObsCore(C, E)
~~~

Here `Verify` means a Lean-checked pass-correctness theorem **instantiated for the actual pass and its exact input/output**, or a Lean translation validator whose soundness theorem the official Lean kernel checks. A pass receipt, checksum, `proved` label, executable test or external SMT/LLVM analysis **alone** is not `Verify`. Compose genuine theorem evidence through #229's existing authority/obligation ledger; do not add a parallel proof oracle. No unsupported step may be accepted in either mode; an Official receipt requires actual official-kernel verification.

**v0.1.0 per-build proof strategy: witness-guided reflective translation validation.** Define a decidable validator for the actual accepted Core → optimization MidIR → execution MidIR → modeled LLVM module stages, with an additional **untrusted data witness** `W` for each enabled transformation. A witness may describe a rewrite sequence, SSA/value/block/loop simulation map, resource/ownership correspondence, or a justified AD pullback; the validator checks all relevant conditions independently against the **actual** artifacts. The stage witness `W` is **untrusted data**, not itself a Lean theorem. Prove the validator's soundness **for every possible witness** in mathlib-free `VastitasOracle` against independent `VastitasMath` semantics. Every **Official** build discharges `validateStages C Mₒ Mₑ L W = true` **by pinned official-kernel reduction/replay** (`decide`/`rfl`). Default **Fast** may instead trust a pinned nanoda audit of an exported Lean proof of that *same current, fully authenticated* obligation, including environment and exact artifact bytes; the `audit-lean` diagnostic alone cannot do this. Native-evaluation shortcuts such as `native_decide`, `bv_decide`, `Lean.ofReduceBool` or native-evaluation axioms **never discharge Official/Constitutional proof obligations** (#282/#285). Official axiom closure is separately checked; Fast has a reviewed matching axiom policy and mode-specific receipt.

The following is a **specification sketch, not implemented Lean code** (the real theorem quantifies over admitted profile, semantics and explicit premises):

~~~lean
theorem validateStages_sound :
    ∀ (c : Core) (o : OptMidIR) (x : ExecMidIR)
      (l : LLVMModule) (w : StageWitness),
      validateStages c o x l w = true →
      ObsLLVM l ⊑ ObsCore c

-- For each Official build, official-kernel-check on *actual* artifacts:
-- For Fast, nanoda-audit authentically bound proof of these same obligations.
-- validateStages C Mₒ Mₑ L W = true
-- printLLVM L = B     (B is the complete emitted .ll byte sequence)
-- parseLLVMSubset B = .ok L
~~~

A bounded Lean-defined subset printer/parser must have a kernel-checked round-trip theorem `parseLLVMSubset (printLLVM L) = .ok L` for valid modeled modules. The per-build check additionally compares **the complete final file bytes** to the reflected `B` before LLVM invocation; a digest only identifies them, and the handoff/OS file-I/O behavior remains an explicit host premise. **The in-process libLLVM parser through `llvm-sys` is not verified** by the Lean round-trip theorem: the parser receiving the **same complete audited bytes** and agreeing with the modeled subset grammar is a labeled external premise, backed by differential tests including optional `llvm-as`, never a kernel proof.

**Compositional granularity.** Prefer per-function validation and bounded per-pass witnesses where justified. Prove the *separate* module/link composition theorem, checking actual call graph, function/nominal identity, ABI, import/FFI and effect contracts, shared memory/ownership, global state and initialization. Function-local success **without** this interface/link verification never justifies a whole-program mode receipt. For an unmodeled cross-function transformation, reject or validate at a proved larger scope. #339 may later partition candidate evidence by function but a cache hit cannot bypass fresh current-run validation.

Official kernel reduction inspects data scaling with each checked artifact/witness and may be expensive for large `String`/`Array`/`ByteArray` values. Benchmark validation time and memory for *both* per-function and final-composition checks; improve checked data representations without replacing reduction by native-evaluation axioms or weakening fail-closed behavior.

The observation/refinement relation must **explicitly** specify the supported program outputs, return/failure/error behavior, divergence (where modeled), observable effects and order, allocation/ownership safety, exact integer behavior and declared floating semantics (operation order, rounding, flags, traps and allowed nondeterminism). For nondeterministic allowed behaviors, use an explicitly stated trace-refinement relation; do not assert byte-equality of all possible executions. Conditional foreign-runtime/ABI assumptions must be visible and never be mislabeled a proof of those components.

The finite supported LLVM IR subset needs a Lean-defined semantic/typing correspondence, including target layout and all emitted instruction/attribute semantics. In particular:

- No unsupported `undef`/`poison`/`freeze` use or unmodeled undefined behavior. A promise such as `nsw`/`nuw`/`exact`/`disjoint`/`inbounds`, `nonnull`/`noalias`/`nocapture`/`readonly`-style memory/capture attributes or fast-math flags may only be emitted with a **discharged kernel-checked obligation** proving it valid on **every admitted Core execution** under the declared numerical/ownership profile. An unjustified flag may introduce poison, UB or observably altered floating behavior, even if a test passes. For v0.1.0, leave the baseline promises disabled until separately modeled and admitted; do not silently enable an LLVM optimization attribute. In particular, scoped `noalias` requires its own memory-model proof, not merely a Rust-side borrow label. Guards and explicit vector operations in execution MidIR can provide checked optimization opportunities without unproved alias promises.
- Preserve arbitrary-precision Nat/Int where admitted (do not silently narrow), nominal and region-based safety even after metadata erasure, function/ABI identity, and explicit external calls.
- Verify **the actual emitted `.ll` bytes** by a bounded independent Lean-side parse/check or equivalent proven emitter-plus-round-trip correspondence, bound to compiler/version/target/options. Merely proving correctness of a pre-printer AST or naming a digest does not establish what LLVM receives.
- The `llvm-sys` adapter may have libLLVM parse, optimize and lower the checked `.ll` to object code, but **no in-process or external LLVM transformation** inherits the Lean-to-LLVM-IR theorem. Any LLVM-produced changed module is an unverified host artifact unless separately checked; optional CLI `opt` output is treated identically.

**Observation model and explicit external premises.** The v0.1.0 admitted profile and each receipt must fix, before an Official check (and corresponding Fast audit):

- **Resource exhaustion:** either define Core-observable allocation failure/stack exhaustion and prove refinement, or state a labeled sufficient-memory/stack premise. Do not silently count arbitrary host crashes as successful refinement.
- **Exact arithmetic:** preserve mathematical Nat/Int semantics at the LLVM-model level. If representation uses GMP or any other foreign big-integer runtime, record the exact ABI, function contracts and external-correctness premise; it does **not** become kernel-proved merely because the call instruction is verified. A runtime compiled through the checked chain could receive a stronger internal guarantee only after its own proof.
- **Floating observations (two distinct admitted routes):** Ordinary LLVM `fadd`/`fmul`/etc. assume **round-to-nearest, ties-to-even**, subnormals preserved, traps disabled and IEEE status flags unobservable. Their operations may be speculated; **without fast-math flags this does not permit arbitrary changes to non-NaN result bits or reassociation that changes them**. Admit ordinary instructions only for a separately named LLVM-default observation profile whose Core effects agree with those assumptions.
- **Observable IEEE effects (#318/#322):** `monad::float` and a bit-exact `std::ieee754` reference may expose operation-local/cumulative flags, failure/short-circuit order, directed/dynamic rounding, traps or represented NaN bits. **Do not silently downgrade that contract to the LLVM-default profile.** A mode-verified lowering must use a separately modeled and verified realization: e.g. constrained FP intrinsics in appropriately `strictfp` functions with `fpexcept.strict`/declared rounding **for all FP operations in each constrained function**, or verified software/reference operations that return results and flags as explicit data. Runtime rounding-mode setup, status-register access, trapping behavior and foreign calls remain labeled host premises where relevant. If unavailable or unproved, reject this profile in either `fast` or `official` `build` (never fabricate `emptyFlags` or claim unavailable flags are known).
- **NaN rule:** LLVM arithmetic NaN signs/payloads are nondeterministic within its documented allowed set, while `bitcast`, `fneg`, `llvm.fabs` and `llvm.copysign` preserve underlying representation except intended sign-bit changes. A value-level **quotient of arithmetic NaN sign/payload** is permitted only in a named profile with a proved *contextually congruent* observation relation and no admitted downstream bit/payload/sign inspection. Otherwise model the permitted NaN outcome **relation** or explicitly normalize/construct the declared bits with a checked implementation. `pure`, representation identity, signed zero, explicit sign operations and #318's representation-exact equality are **not globally quotiented**. Even constrained intrinsics do not automatically establish a chosen bit-exact NaN propagation policy. Reject a deterministic bit-exact Core → ordinary-LLVM arithmetic lowering unless the required refinement is shown. Never silently enable fast-math.
- **Toolchain receipt:** record the locked `llvm-sys` version and actual libLLVM build/link mode/identity, C-API parser/pass/target-machine/codegen configuration, exact options (including contraction policy if applicable), target triple, data layout, runtime/ABI identities, linker executable/argv, environment, every generated input and any optional `llvm-as`/`opt`/`llc` diagnostics. This is reproducibility metadata, **not** proof of the host toolchain.

An **`official` build must fail closed before LLVM invocation** if any applicable internal translation step, emitted LLVM construct or exact-output correspondence lacks discharged evidence. `vastitas check` may still report independently accepted source without claiming an officially verified native executable. Unverified experimental lowering, if offered, must be explicit and outside `official` `build`.

## 4. Transparency records, caches and visibility

**Two channels from one real pass event, not one trusted diagnostic receipt.** The proof-side **`StageWitness`** is untrusted, typed/bounded data submitted with actual before/after artifacts to a sound Lean validator. The internal acceptance record binds function/pass identity, input/output artifacts, checked witness and validation result. A forged/mismatched witness or changed semantic artifact makes `official` `build` fail closed (and must fail Fast's corresponding bound audit). Independently **project** #414's versioned *diagnostic* receipt from the observed pass event and checked status: source/selected-method and artifact identities, applied/skipped/failed reason, exact obligation/evidence status, final `.ll` bytes, actual `llvm-sys`/libLLVM calls, flags/linker inputs and labeled foreign/parser/resource premises. The diagnostic report is **not** the witness, nor a theorem or validator input. Its own parser/serialization/format failure remains a **diagnostic-only error** by #414/#416, never a new source rejection or permission to build. A false proof-bearing identity must fail validation; a misleading/corrupt optional report is flagged without changing an otherwise independently verified build. `proved / conditional / unverified / unknown` are report states, not proof authority. The normalized DAG describes actual events, never aspirational passes.

`--explain=text|json` and IR inspection (#415/#416) observe only the diagnostic projection and do not influence acceptance, code generation or proof status. Cache behavior (#339) must independently reconstruct current accepted Core and rerun all v0.2.0 Vastitas-owned IR/emission passes; only protected, authenticated **per-CGU in-process libLLVM native object results** (with optional fully matching link output) may be reused under its separate authorization/key. Its input key is the **exact LLVM `.ll` and associated emitted files** plus pinned `llvm-sys`/libLLVM/linker/environment/ABI inputs, **not** the historical `Main.lean` emitter. Cache bytes never prove a theorem.

## 5. LLVM semantics cross-check (Bridge only; not proof authority)

The LLVM subset denotation is defined in mathlib-free `VastitasMath`; the actual validator/emitter is in `VastitasKernel`; the checked correspondence theorem is in mathlib-free `VastitasOracle` (#285). `VastitasKernel` must not import the mathematical specification or `VastitasOracle`; build orchestration may request a separate kernel check of Oracle evidence. This split does **not** prove our LLVM model is identical to LLVM's implementation.

[lean-mlir](https://github.com/opencompl/lean-mlir) provides useful independent integer/poison/refinement semantics for a possible `VastitasBridge` conformance theorem on the **shared fragment**, not a dependency for `check`/`build` or a replacement for the authoritative model. At reviewed revision `b8c4a77`, its LLVM semantics use `PoisonOr (BitVec w)` and reference the root `SSA` package and Mathlib; the package pins an incompatible 2025-12-01 Lean nightly, while Vastitas pins Lean 4.35.0. **Do not add an unconditional Lake dependency.** A separately vetted Bridge experiment must pin a compatible revision/fork or attributed minimal extracted definitions, audit import closure and licenses, and reject any theorem using `Lean.ofReduceBool`/native-evaluation axioms in its proof closure. Even a successful Bridge conformance proof covers only its stated integer fragment and cannot discharge parser/native-backend premises. [Vellvm](https://github.com/vellvm/vellvm) is additional semantics prior art; Alive2 results can be attached only as **non-proof diagnostics**.

## 6. v0.1.0 release acceptance

The **first implementation scope** is every executable construct admitted by the declared v0.1.0 finite profile (including #462's unified finite `fn` model when implemented); it does **not** move #405's generic `Vec<T>`/loop/ADT or #408's general type/const specialization from v0.2.0 into v0.1.0. Later language features must extend this same verified route and registry.

- [ ] **Spec and representations:** implement the phase-indexed MidIR v1 Lean constructors, validators, versioned serialization, deterministic printer/parser and rejection of forged/stale/ill-typed/illegal-resource direct-IR candidates; reserve typed disabled-by-default LLVM promise slots.
- [ ] **Real pipeline:** connect accepted `.vast` Core → optimization MidIR → execution MidIR → emitted LLVM `.ll` on the actual `check/build` path; identify the exact final emitted LLVM bytes, target triple, data layout, ABI, `llvm-sys`/`libLLVM` revision and pass/target-machine options. Integrate the pinned **Cargo/`llvm-sys` in-process production backend** and qualify LLVM 23.1.4 (initial candidate), static-linked release packaging and Linux/macOS native builds; old Lean/C remains an explicitly marked legacy/differential path only.
- [ ] **Formal transparency:** implement witness-guided reflective stage validators with `∀ W` soundness, **per-function** obligations plus checked module/call/ABI/effect composition; discharge **Official** current-run checks **by kernel reduction** and **Fast** current-run proof checks by pinned nanoda audit of current input-bound evidence including exact LLVM printer/parser/last-file-byte correspondence and axiom audit. Keep diagnostic reports independent of the proof-input path. No `native_decide`/`Lean.ofReduceBool`, `unknown`, `conditional` or `unverified` **internal** preservation gap may pass either build mode. Keep external host/FFI assumptions disclosed.
- [ ] **Adversarial tests:** Rust/source-wire spoofing; altered MidIR identity, owner, method winner, specialization, loans, CFG, witness/value/loop/AD simulation maps, proofs; tampered LLVM bytes, ABI, attributes, alias claims, numeric policy, native-evaluation proof bypass and missing evidence all fail closed. Test per-function false witnesses and a valid local witness with invalid inter-function ABI/effect composition; malformed *diagnostic-only* receipts do **not** change the independent mode-specific proof result. Test LLVM-default FP against observable-flags/traps/directed-rounding rejection, NaN bitcast/sign inspection, constrained-FP subset, parser disagreement and admissible real resource/numeric paths.
- [ ] **User-visible boundary:** source `check` without native steps, explicit Fast/Official verification receipts and rejected `build`, opt-in accurate diagnostic trace without proof authority; pin the finite v0.1.0 LLVM-default versus `monad::float` FP admission profiles and explicitly document resource, foreign big-int, NaN, flag/trap/rounding, LLVM-parser and toolchain premises. Linux/macOS native tests, libLLVM parser checks and optional `llvm-as` comparisons are diagnostics, not theorem substitutes.
- [ ] **Quality measurements:** compare actual LLVM-backed execution against matched C/C++ for time, allocations/copies and peak memory (#222) without treating use of LLVM or a benchmark as a correctness or performance theorem.

**Dependencies and scope:** #152 (later Lean-native frontend), #184/#192 (constitutional CS/MS/CF), #229 (authority/obligation ledger), #350 (Charter), #339 (v0.2.0 cache), #389/#405 (algorithm/Core), #414–#416 (diagnostics), #418/#419/#420 (layer contracts), #462 (v0.1.0 finite `fn`). The official Lean kernel remains the only formal/Constitutional proof authority, while nanoda is the explicitly trusted operational auditor for default Fast; no new Domain Checker, second semantic Core, user-facing `unsafe`, stable public IR ABI, completed proof, native binary guarantee, or measured C/C++ parity is implied by this specification.
