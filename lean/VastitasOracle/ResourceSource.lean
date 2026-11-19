import VastitasKernel.ResourceProtocol
import VastitasOracle.StorageFunctions
import VastitasOracle.IndexedAuthority
import VastitasOracle.IndexedSource
import VastitasOracle.IndexedProgramSafety

/-! Public resource/source composition facts, tied to actual reconstruction and
both independent checkers. Pure-Core totality does not establish mutable native
heap semantics, source operational correspondence or numerical correctness. -/
namespace VastitasOracle.ResourceSource
open VastitasKernel VastitasKernel.ResourceSource
open VastitasKernel.Storage VastitasKernel.Indexed

theorem exact_components {program : Program} (checked : Checked program requireMain) :
    Indexed.AuthoritySource.checkProgram program.pureProgram (requireMain && program.entry.isNone) = .ok checked.pureProgram ∧
    lower program = .ok checked.lowered ∧
    Functions.checkLibrary checked.lowered.functions (numericalEnvironment checked.pureProgram) checked.targets.signatures = .ok checked.library :=
  ⟨checked.pureAccepted, checked.reconstructed, checked.libraryAccepted⟩

theorem complete_resource_identity {program : Program} (checked : Checked program requireMain) :
    checked.lowered.owners = program.owned.map Prod.fst ∧
    checked.lowered.functions.map Functions.Function.id = List.range program.owned.length ∧
    checked.lowered.functions.length = program.owned.length := by
  refine ⟨checked.provenance.1, checked.provenance.2.1, ?_⟩
  have length := congrArg List.length checked.provenance.2.1
  simpa using length

theorem call_provenance {program : Program} (checked : Checked program requireMain)
    (reference : Reference) (member : reference ∈ checked.lowered.references) :
    (program.owned[reference.caller]?).map (fun entry => entry.1.scope) = some reference.scope ∧
    reference.target.kind = .resourceFunction ∧
    (Namespace.resolve program.pureProgram.source.headers.indexed reference.scope reference.path.path reference.path.span).toOption = some reference.target ∧
    (program.owned[reference.callee]?).map Prod.fst = some reference.target.owner :=
  checked.provenance.2.2.1 reference member

theorem numerical_provenance {program : Program} (checked : Checked program requireMain)
    (reference : NumericalReference) (member : reference ∈ checked.lowered.numericalReferences) :
    (program.owned[reference.caller]?).map (fun entry => entry.1.scope) = some reference.reference.scope ∧
    reference.reference.Valid program.pureProgram.source.headers.indexed :=
  checked.provenance.2.2.2 reference member

theorem every_resource_body {program : Program} (checked : Checked program requireMain)
    (function : Functions.Function) (member : function ∈ checked.lowered.functions) :
    ∃ result ∈ checked.library.bodies, result.function = function.id ∧
      Functions.probe checked.lowered.functions function (numericalEnvironment checked.pureProgram) checked.targets.signatures = .ok result ∧
      Storage.checkPlan result.statements = .ok result.resources :=
  StorageFunctions.every_library_body checked.library member

theorem original_authority {program : Program} (checked : Checked program requireMain) :
    Authority.Trace program.pureProgram.source.headers.indexed checked.pureProgram.authority.headers.assembled.prepared {}
      checked.pureProgram.authority.headers.assembled.prepared.core.assembly.events
      checked.pureProgram.authority.headers.assembled.state ∧
    Authority.Exclusive checked.pureProgram.authority.headers.assembled.state ∧
    checked.pureProgram.authority.headers.assembled.state.loans = [] :=
  IndexedAuthority.authority_trace checked.pureProgram

theorem pure_value_bodies_typed {program : Program} (checked : Checked program requireMain) :
    Core.Typing.ModuleTyped checked.values.audit.lowered.module ∧
    Core.Typing.ModuleTyped checked.values.executable.lowered.module :=
  ⟨(IndexedFunctions.checked_pass checked.values.audit).2.2.1,
    (IndexedFunctions.checked_pass checked.values.executable).2.2.1⟩

/-- Pure value bodies called from a resource entry. The mixed emit path generates
their library from `checked.values.compiled.core`, this module with its
reverse passes compiled into Core (#623). -/
theorem pure_value_functions_total {program : Program} (checked : Checked program requireMain) :
    ∀ function ∈ checked.values.executable.core.module.functions,
      IndexedFunctionSafety.FunctionReturns checked.values.executable.core.module function :=
  IndexedProgramSafety.checked_functions_total_and_typed checked.values.executable.core

/-- Without a resource entry, the emit path generates code from
`checked.pureProgram.compiled.core`, this module with its reverse passes
compiled into Core (see `ResourceCodegen.generated_pure_entry`). Every function
of this module has typed, finite evaluation. -/
theorem pure_entry_functions_total {program : Program} (checked : Checked program requireMain) :
    ∀ function ∈ checked.pureProgram.executable.core.module.functions,
      IndexedFunctionSafety.FunctionReturns checked.pureProgram.executable.core.module function :=
  IndexedProgramSafety.checked_functions_total_and_typed checked.pureProgram.executable.core

private theorem main_total_of {required : Bool} (core : Core.Typing.CheckedModule required)
    (same : required = true) :
    ∃ id function result,
      core.module.main = some id ∧
      core.module.functions.find? (fun function => function.id == id) = some function ∧
      IndexedEvaluation.Evaluates core.module (fun _ => none) function.body (.integer result) := by
  subst same
  exact IndexedProgramSafety.checked_main_total core

/-- A pure-entry program accepted with a required `main` has a parameterless
`main` whose body evaluates to an `Int` in the actual indexed evaluator. -/
theorem pure_entry_main_total {program : Program} (checked : Checked program true)
    (found : program.entry = none) :
    ∃ id function result,
      checked.pureProgram.executable.core.module.main = some id ∧
      checked.pureProgram.executable.core.module.functions.find? (fun function => function.id == id) =
        some function ∧
      IndexedEvaluation.Evaluates checked.pureProgram.executable.core.module (fun _ => none)
        function.body (.integer result) :=
  main_total_of checked.pureProgram.executable.core (by simp [found])

/-- The accepted public entry uses the original library's complete probe list
and starts executable expansion from the actual closed program. -/
theorem entry_uses_checked_library {program : Program} (checked : Checked program requireMain)
    (entry : Nat) (found : program.entry = some entry) :
    let p : Functions.Program := ⟨checked.lowered.functions, entry⟩
    let e := checked.execution entry found
    Functions.checkWithLibrary p checked.library = .ok e.checked ∧
      e.checked.bodies = checked.library.bodies ∧
      Functions.executable p (numericalEnvironment checked.pureProgram) checked.targets.signatures =
        .ok e.checked.context := by
  let e := checked.execution entry found
  let p : Functions.Program := ⟨checked.lowered.functions, entry⟩
  have reused := Functions.checkWithLibrary_eq_check p checked.library
  have same : e.checked.bodies = checked.library.bodies :=
    Except.ok.inj (e.checked.bodiesFrom.symm.trans checked.library.bodiesFrom)
  exact ⟨reused.trans e.accepted, same, e.checked.expanded⟩

theorem library_work_bound {program : Program} (checked : Checked program requireMain) :
    (checked.library.bodies.map Functions.Probe.units).sum = checked.library.work.val ∧
      checked.library.work.val ≤ Limits.resourceWork := by
  have total := (Work.collect_exact checked.library.collected).2
  exact ⟨by simpa [Work.zero] using total.symm, Nat.le_of_lt_succ checked.library.work.isLt⟩

theorem entry_work_bound {program : Program} (checked : Checked program requireMain)
    (entry : Nat) (found : program.entry = some entry) :
    let e := (checked.execution entry found).checked
    (checked.library.bodies.map Functions.Probe.units).sum + e.context.work.val +
      e.resources.work.val + e.shapes.resources.work.val ≤ Limits.resourceWork := by
  have same := (entry_uses_checked_library checked entry found).2.1
  rw [← same]
  exact (checked.execution entry found).checked.workBound

theorem actual_entry_closed {program : Program} (checked : Checked program requireMain)
    (entry : Nat) (found : program.entry = some entry) :
    let execution := checked.execution entry found
    Functions.check ⟨checked.lowered.functions, entry⟩ (numericalEnvironment checked.pureProgram) checked.targets.signatures = .ok execution.checked ∧
    Storage.run 4096 {} execution.checked.statements = .ok execution.checked.resources.finalState ∧
    execution.checked.resources.finalState.allocations = [] ∧ execution.checked.resources.finalState.loans = [] :=
  ⟨(checked.execution entry found).accepted, (checked.execution entry found).checked.resources.accepted,
    (checked.execution entry found).checked.resources.closed⟩

theorem namespace_work_bound {json : Lean.Json} (input : VastitasKernel.ResourceSource.Wire.CheckedInput json requireMain) :
    Namespace.priceInput input.input.pureProgram.source.headers.indexed json = .ok input.namespaceReceipt.inputUnits ∧
    input.namespaceReceipt.inputUnits.val + VastitasKernel.ResourceSource.Wire.namespaceUnits input.checked ≤ Limits.namespaceProgramWork :=
  ⟨input.namespaceReceipt.priced, input.namespaceReceipt.bounded⟩

/-- The checked entry file's lexical projection agrees with the structured
wire commands. Expanding either yields the exact events and spans in the
independently accepted authority trace. File acquisition and the non-edit
grammar are frontend premises. -/
theorem structured_assembly_trace {json : Lean.Json} (input : Wire.CheckedInput json requireMain) :
    let a := input.checked.pureProgram.authority.headers.assembled
    ∃ file items trace, AssemblySource.rootFile json = .ok file ∧
      AssemblyText.parse file.text file.offset = .ok items ∧
      AssemblySource.read json = .ok items ∧ AssemblySource.expand items = .ok trace ∧
      trace.events = a.prepared.core.assembly.events ∧
      trace.span.all (· == a.prepared.core.assembly.span) = true ∧
      VastitasKernel.Authority.Trace _ a.prepared {} trace.events a.state := by
  let source := input.assemblySource
  refine ⟨source.file, source.items, source.trace, source.supplied, source.lexical,
    source.decoded, source.expanded, source.exactEvents, source.exactSpan, ?_⟩
  rw [source.exactEvents]
  exact (VastitasOracle.Authority.assembled_trace _).1

/-- Supplying a revision cannot select a method. Acceptance implies exact
equality with the complete receipt reconstructed from this program's checked
authority and Core passes. No claim about LLVM or native execution follows. -/
theorem expected_function_revision_exact {json expected : Lean.Json}
    (input : Wire.CheckedInput json requireMain)
    (supplied : json.getObjVal? "expected_function_revision" = .ok expected) :
    expected.compress = (FunctionRevision.artifact (Wire.revisionInput json) input.checked).compress := by
  have h := input.revisionMatches
  simp only [Wire.RevisionMatches, supplied] at h
  exact h.2.2

/-- At this same replayed revision the source owner/key selects the exact
method and definition of each executable dispatch edge; the callee symbol
is the specialization emitted for that definition. -/
theorem expected_revision_selects_method {json expected : Lean.Json}
    (input : Wire.CheckedInput json requireMain)
    (supplied : json.getObjVal? "expected_function_revision" = .ok expected)
    (call : FunctionSource.Compiler.DispatchCall)
    (member : call ∈ input.checked.pureProgram.executable.lowered.dispatchCalls) :
    expected.compress = (FunctionRevision.artifact (Wire.revisionInput json) input.checked).compress ∧
    input.checked.pureProgram.executable.lowered.origins[call.emittedId]? =
      some (FunctionSource.Compiler.Key.mk call.definition []) ∧
    ∃ family, input.checked.pureProgram.compiler.input.dispatch.families[call.target.owner]? = some family ∧
      call.key ∈ family.domain ∧
      Dispatch.Selection family.nominals.hierarchy family.checked.methods call.key (some call.method) ∧
      input.checked.pureProgram.compiler.input.dispatch.definitions[(call.method, call.key)]? = some call.definition :=
  ⟨expected_function_revision_exact input supplied,
    IndexedDispatch.dispatch_call_emitted input.checked.pureProgram.executable call member,
    (IndexedDispatch.dispatch_call_selected input.checked.pureProgram.executable call member).2.2.2⟩

theorem public_input {json : Lean.Json} (input : VastitasKernel.ResourceSource.Wire.CheckedInput json requireMain) :
    VastitasKernel.ResourceSource.Wire.program json = .ok input.input ∧
    VastitasKernel.ResourceSource.check input.input requireMain = .ok input.checked ∧
    lower input.input = .ok input.checked.lowered :=
  ⟨input.decoded, input.accepted, input.checked.reconstructed⟩

/-- The public wire uses the same numerical declaration contract as the
actual complete authority checker. This is not a floating-point result theorem. -/
theorem public_numerical_declaration {json : Lean.Json}
    (input : VastitasKernel.ResourceSource.Wire.CheckedInput json requireMain)
    (id marker : DeclId) (representation : Indexed.Representation) (capabilities : List Capability)
    (member : ⟨id, .implementation marker representation capabilities⟩ ∈
      input.checked.pureProgram.authority.headers.declarations.resolved.declarations.indexed) :
    representation.Valid input.checked.pureProgram.authority.headers.declarations.resolved.declarations.indexed
      marker capabilities :=
  (IndexedSource.checked_implementation_contract _ input.checked.pureProgram.authority.headers.declarations
    id marker representation capabilities member).2.2

/-- The public protocol checks every named functor, including unused ones,
in its own accepted declaration environment at the input's checked revision. -/
theorem public_finite_functor {json : Lean.Json} (input : Wire.CheckedInput json requireMain)
    (member : ⟨owner, .finiteFunctor schema maps⟩ ∈
      input.checked.pureProgram.authority.headers.declarations.resolved.declarations.indexed) :
    let env := input.checked.pureProgram.authority.headers.declarations.resolved.declarations.indexed
    Wire.RevisionMatches json input.checked ∧
      ∃ m, Indexed.FiniteFunctors.model (Indexed.FiniteCategories.view env) schema maps = some m ∧
        VastitasOracle.FiniteFunctors.Preserves m :=
  ⟨input.revisionMatches, VastitasOracle.FiniteFunctors.checked_functor
    input.checked.pureProgram.authority.headers.declarations member⟩

/-- The named isomorphism uses the category, arrows and both identities of
this accepted public input. The same revision covers the unused declarations. -/
theorem public_finite_iso {json : Lean.Json} (input : Wire.CheckedInput json requireMain)
    (member : ⟨owner, .finiteIso schema fields⟩ ∈
      input.checked.pureProgram.authority.headers.declarations.resolved.declarations.indexed) :
    let env := input.checked.pureProgram.authority.headers.declarations.resolved.declarations.indexed
    Wire.RevisionMatches json input.checked ∧
      ∃ m, Indexed.FiniteIso.select (Indexed.FiniteCategories.view env) schema fields = .ok m ∧
        VastitasOracle.FiniteIso.Inverses m :=
  ⟨input.revisionMatches, VastitasOracle.FiniteIso.checked_iso
    input.checked.pureProgram.authority.headers.declarations member⟩

/-- A transformation in the accepted module satisfies all its component
endpoint and naturality equations under the very same checked revision. -/
theorem public_finite_nat_trans {json : Lean.Json} (input : Wire.CheckedInput json requireMain)
    (member : ⟨owner, .finiteNatTrans schema fields⟩ ∈
      input.checked.pureProgram.authority.headers.declarations.resolved.declarations.indexed) :
    let env := input.checked.pureProgram.authority.headers.declarations.resolved.declarations.indexed
    Wire.RevisionMatches json input.checked ∧
      ∃ m, Indexed.FiniteNatTrans.model (Indexed.FiniteCategories.view env) schema fields = some m ∧
        VastitasOracle.FiniteNatTrans.Natural m :=
  ⟨input.revisionMatches, VastitasOracle.FiniteNatTrans.checked_transformation
    input.checked.pureProgram.authority.headers.declarations member⟩

/-- A named Monad of the public checked module satisfies both unit laws
and associativity for the structure selected by this exact input revision. -/
theorem public_finite_monad {json : Lean.Json} (input : Wire.CheckedInput json requireMain)
    (member : ⟨owner, .finiteMonad schema fields⟩ ∈
      input.checked.pureProgram.authority.headers.declarations.resolved.declarations.indexed) :
    let env := input.checked.pureProgram.authority.headers.declarations.resolved.declarations.indexed
    Wire.RevisionMatches json input.checked ∧
      ∃ m, Indexed.FiniteMonads.model (Indexed.FiniteCategories.view env) schema fields = some m ∧
        VastitasOracle.FiniteMonads.Diagrams m :=
  ⟨input.revisionMatches, VastitasOracle.FiniteMonads.checked_monad
    input.checked.pureProgram.authority.headers.declarations member⟩

/-- Every actual product receipt belongs to the environment returned by this
same public source check, and records its own exact emitted resource operation. -/
theorem public_product_origin {json : Lean.Json}
    (input : VastitasKernel.ResourceSource.Wire.CheckedInput json requireMain)
    (entry : Nat) (found : input.input.entry = some entry)
    (receipt : Functions.NumericalReceipt)
    (member : receipt ∈ (input.checked.execution entry found).checked.context.products.toList) :
    receipt.environment = numericalEnvironment input.checked.pureProgram ∧
    Storage.Numerical.checkProduct receipt.environment receipt.resources receipt.values
      receipt.left receipt.right receipt.output receipt.mode receipt.policy receipt.alpha receipt.beta = .ok receipt.checked ∧
    receipt.priorCode ++ [.action (.gemm (receipt.checked.product.request receipt.mode receipt.policy))] = receipt.code ∧
    Storage.checkAction receipt.resources (.gemm (receipt.checked.product.request receipt.mode receipt.policy)) = .ok receipt.after :=
  ⟨(input.checked.execution entry found).numericalOrigins.2 receipt member,
    receipt.accepted, receipt.emitted, receipt.transitioned⟩

/-- Dependent inputs use the exact declaration environment accepted by the
same public request. Their certificates are from actual expansion, not probes. -/
theorem public_numerical_input_origin {json : Lean.Json}
    (input : VastitasKernel.ResourceSource.Wire.CheckedInput json requireMain)
    (entry : Nat) (found : input.input.entry = some entry)
    (receipt : Functions.NumericalInputReceipt)
    (member : receipt ∈ (input.checked.execution entry found).checked.context.inputs.toList) :
    receipt.environment = numericalEnvironment input.checked.pureProgram ∧
    Storage.Numerical.checkInput receipt.environment receipt.callerResources receipt.callerValues
      receipt.input receipt.actual = .ok receipt.checked ∧
    Functions.NumericalBinding receipt.checked.value receipt.actual receipt.bound receipt.access
      receipt.before receipt.after receipt.values :=
  ⟨(input.checked.execution entry found).inputOrigins receipt member, receipt.accepted, receipt.binding⟩

theorem public_numerical_result_origin {json : Lean.Json}
    (input : VastitasKernel.ResourceSource.Wire.CheckedInput json requireMain)
    (entry : Nat) (found : input.input.entry = some entry)
    (receipt : Functions.NumericalResultReceipt)
    (member : receipt ∈ (input.checked.execution entry found).checked.context.outputs.toList) :
    receipt.environment = numericalEnvironment input.checked.pureProgram ∧
    Storage.Numerical.checkInput receipt.environment receipt.resources receipt.values
      (.ownedMap receipt.source receipt.target) receipt.actual = .ok receipt.checked ∧
    receipt.checked.value = .ownedMap receipt.view ∧ receipt.returned.map = some receipt.view :=
  ⟨(input.checked.execution entry found).outputOrigins receipt member,
    receipt.accepted, receipt.selected, receipt.mapping⟩

theorem public_numerical_transform_origin {json : Lean.Json}
    (input : VastitasKernel.ResourceSource.Wire.CheckedInput json requireMain)
    (entry : Nat) (found : input.input.entry = some entry)
    (receipt : Functions.TransformReceipt)
    (member : receipt ∈ (input.checked.execution entry found).checked.context.transforms.toList) :
    receipt.environment = numericalEnvironment input.checked.pureProgram ∧
    Storage.Numerical.checkTransform receipt.environment receipt.resources receipt.values receipt.name receipt.parent
      receipt.child receipt.operation = .ok receipt.checked ∧ receipt.checked.after = receipt.after :=
  ⟨(input.checked.execution entry found).transformOrigins receipt member, receipt.accepted, receipt.transitioned⟩

theorem public_vector_conjugation_origin {json : Lean.Json}
    (input : VastitasKernel.ResourceSource.Wire.CheckedInput json requireMain)
    (entry : Nat) (found : input.input.entry = some entry)
    (receipt : Functions.VectorConjugateReceipt)
    (member : receipt ∈ (input.checked.execution entry found).checked.context.vectorConjugates.toList) :
    receipt.environment = numericalEnvironment input.checked.pureProgram ∧
    Storage.Numerical.checkVectorConjugate receipt.environment receipt.resources receipt.values receipt.name receipt.parent
      receipt.child receipt.basis receipt.selected = .ok receipt.checked :=
  ⟨(input.checked.execution entry found).vectorOrigins receipt member, receipt.accepted⟩

theorem public_evaluation_origin {json : Lean.Json}
    (input : VastitasKernel.ResourceSource.Wire.CheckedInput json requireMain)
    (entry : Nat) (found : input.input.entry = some entry)
    (receipt : Functions.EvaluationReceipt)
    (member : receipt ∈ (input.checked.execution entry found).checked.context.evaluations.toList) :
    receipt.environment = numericalEnvironment input.checked.pureProgram ∧
    Storage.Numerical.checkEvaluation receipt.environment receipt.resources receipt.values receipt.left receipt.right
      receipt.output receipt.leftChild receipt.rightChild receipt.operation receipt.mode receipt.policy receipt.alpha receipt.beta = .ok receipt.checked :=
  ⟨(input.checked.execution entry found).evaluationOrigins receipt member, receipt.accepted⟩

end VastitasOracle.ResourceSource
