import VastitasOracle.IndexedDispatch
import VastitasKernel.IndexedAcceptance
import VastitasKernel.LegacySource
import VastitasKernel.ResourceProtocol

/-! Converse call coverage on the exact Core returned by each public protocol.
The matching unit is a caller specialization and emitted target ID, counted
with multiplicity. This is not a source-location bijection, operational
correspondence, numerical receipt coverage or native refinement. -/
namespace VastitasOracle.CallCoverage
open VastitasKernel VastitasKernel.Indexed FunctionSource.Compiler

def Returned {prepared : PreparedProgram} (checked : CheckedPass prepared audit requireMain) : Prop :=
  ∀ function ∈ checked.core.module.functions, ∀ target ∈ function.body.callIds,
    let pass := checked.lowered
    let edge : CallEdge := (pass.origins[function.id]?, target)
    (coreCallEdges pass).countP (· == edge) = (emittedCallEdges pass).countP (· == edge) ∧
    (∃ call ∈ pass.emittedCalls, pass.origins[function.id]? = some call.caller ∧
      call.id = target ∧ pass.origins[target]? = some call.origin) ∧
    ∀ (origin : Key) (selection : Nat × Dispatch.Key), pass.origins[target]? = some origin →
      prepared.input.dispatch.definitions[selection]? = some origin.definition →
      (coreDispatchEdges prepared.input pass).countP (· == edge) =
        (dispatchCallEdges pass).countP (· == edge) ∧
      ∃ call ∈ pass.dispatchCalls,
        pass.origins[function.id]? = some call.caller ∧ call.emittedId = target ∧
        pass.origins[target]? = some (Key.mk call.definition []) ∧
        ∃ family, prepared.input.dispatch.families[call.target.owner]? = some family ∧
          call.key ∈ family.domain ∧
          Dispatch.Selection family.nominals.hierarchy family.checked.methods call.key (some call.method) ∧
          prepared.input.dispatch.definitions[(call.method, call.key)]? = some call.definition

theorem returned {prepared : PreparedProgram} (checked : CheckedPass prepared audit requireMain) :
    Returned checked := by
  intro function present target called
  rw [checked.coreInput] at present
  refine ⟨IndexedFunctions.core_call_count checked function present target called, ?_, ?_⟩
  · obtain ⟨call, member, caller, same⟩ := IndexedFunctions.core_call_recorded checked function present target called
    exact ⟨call, member, caller, same, same ▸ IndexedFunctions.emitted_call_origin checked call member⟩
  · intro origin selection found selected
    have generic := (IndexedDispatch.dispatch_target_iff prepared.input checked.lowered target).mpr
      ⟨origin, found, selection, selected⟩
    exact ⟨IndexedDispatch.core_dispatch_call_count checked function present target called generic,
      IndexedDispatch.core_dispatch_call_selected checked function present target called generic⟩

theorem legacy_wire (input : Indexed.LegacySource.CheckedInput json requireMain) :
    Returned input.checked.audit ∧ Returned input.checked.executable :=
  ⟨returned _, returned _⟩

theorem indexed_wire (input : Wire.CheckedInput json requireMain) :
    Returned input.checked.audit ∧ Returned input.checked.executable :=
  ⟨returned _, returned _⟩

theorem resource_wire (input : VastitasKernel.ResourceSource.Wire.CheckedInput json requireMain) :
    Returned input.checked.pureProgram.audit ∧ Returned input.checked.pureProgram.executable ∧
    Returned input.checked.values.audit ∧ Returned input.checked.values.executable :=
  ⟨returned _, returned _, returned _, returned _⟩

end VastitasOracle.CallCoverage
