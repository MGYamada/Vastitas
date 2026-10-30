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
    Functions.checkLibrary checked.lowered.functions (numericalEnvironment checked.pureProgram) = .ok checked.library :=
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
      Functions.probe checked.lowered.functions function (numericalEnvironment checked.pureProgram) = .ok result ∧
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

theorem pure_value_functions_total {program : Program} (checked : Checked program requireMain) :
    ∀ function ∈ checked.values.executable.core.module.functions,
      IndexedFunctionSafety.FunctionReturns checked.values.executable.core.module function :=
  IndexedProgramSafety.checked_functions_total_and_typed checked.values.executable.core

theorem actual_entry_closed {program : Program} (checked : Checked program requireMain)
    (entry : Nat) (found : program.entry = some entry) :
    let execution := checked.execution entry found
    Functions.check ⟨checked.lowered.functions, entry⟩ (numericalEnvironment checked.pureProgram) = .ok execution.checked ∧
    Storage.run 4096 {} execution.checked.statements = .ok execution.checked.resources.finalState ∧
    execution.checked.resources.finalState.allocations = [] ∧ execution.checked.resources.finalState.loans = [] :=
  ⟨(checked.execution entry found).accepted, (checked.execution entry found).checked.resources.accepted,
    (checked.execution entry found).checked.resources.closed⟩

theorem public_input {json : Lean.Json} (input : VastitasKernel.ResourceSource.Wire.CheckedInput json requireMain) :
    VastitasKernel.ResourceSource.Wire.program json = .ok input.input ∧
    VastitasKernel.ResourceSource.check input.input requireMain = .ok input.checked ∧
    lower input.input = .ok input.checked.lowered :=
  ⟨input.decoded, input.accepted, input.checked.reconstructed⟩

/-- Public protocol 8 uses the same numerical declaration contract as the
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

/-- Every actual product receipt belongs to the environment returned by this
same public source check, and records its own exact emitted resource operation. -/
theorem public_product_origin {json : Lean.Json}
    (input : VastitasKernel.ResourceSource.Wire.CheckedInput json requireMain)
    (entry : Nat) (found : input.input.entry = some entry)
    (receipt : Functions.NumericalReceipt)
    (member : receipt ∈ (input.checked.execution entry found).checked.context.products.toList) :
    receipt.environment = numericalEnvironment input.checked.pureProgram ∧
    Storage.Numerical.checkProduct receipt.environment receipt.resources receipt.values
      receipt.left receipt.right receipt.output receipt.mode receipt.policy = .ok receipt.checked ∧
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

end VastitasOracle.ResourceSource
