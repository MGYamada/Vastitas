import VastitasOracle.ResourceValueFlow
import VastitasOracle.StorageShapeNumerical

/-! Public runtime-shape certificates retain the exact source environment,
scalar-slot liveness and independently replayed caller schedules. Guard
valuations here are mathematical naturals; the Lean/native scalar and UInt64
lowering remain separately tested implementation boundaries. -/
namespace VastitasOracle.ResourceRuntimeShapes
open VastitasKernel Storage

/-- Every referenced dimension comes from an actually live immutable integral
slot at this position in the mixed schedule. A final slot table alone is not
used as evidence that the slot was available earlier. -/
theorem runtime_references {signatures : List ValueFlow.Signature}
    {fuel : Nat} {before after : ValueFlow.State} {event : Shapes.Event}
    {rest : List ValueFlow.Statement}
    (accepted : ValueFlow.run signatures (fuel + 1) before (.runtime event :: rest) = .ok after) :
    event.references.all (Shapes.extentSlot before.slots) = true ∧
    ValueFlow.run signatures fuel before rest = .ok after := by
  simp only [ValueFlow.run, bind, Except.bind, pure, Except.pure] at accepted
  split at accepted
  · rename_i references
    exact ⟨by simpa using references, accepted⟩
  · contradiction

/-- The public entry's actual mixed flow determines the exact symbolic actions.
For every valuation satisfying their emitted operation guards, the original
concrete checker accepts precisely their instantiated schedule and has no
remaining owners or loans. Explicit numerical guards are additional premises
at each selected product below. -/
theorem entry_realizes {program : ResourceSource.Program} {requireMain : Bool}
    (checked : ResourceSource.Checked program requireMain)
    (entry : Nat) (found : program.entry = some entry) (valuation : Shapes.Valuation)
    (guards : Shapes.guardsHold valuation (checked.execution entry found).checked.shapes.resources.guards) :
    let certificate := (checked.execution entry found).checked.shapes
    ∃ concrete,
      Shapes.instantiate valuation 4096 {} (Shapes.Flow.actions certificate.events) = .ok concrete ∧
      Storage.run 4096 {} concrete = .ok (certificate.resources.after.eval valuation) ∧
      auditState (certificate.resources.after.eval valuation) = true ∧
      (certificate.resources.after.eval valuation).allocations = [] ∧
      (certificate.resources.after.eval valuation).loans = [] := by
  let certificate := (checked.execution entry found).checked.shapes
  obtain ⟨concrete, instantiated, executed, audited⟩ := StorageShapes.checked_realizes valuation _ {}
    _ certificate.resources (by simp [Shapes.guardsHold, Shapes.Frame.guards]) guards
  exact ⟨concrete, instantiated, executed, audited,
    by change List.map _ certificate.resources.after.allocations = []; rw [certificate.closed.1]; rfl,
    by change List.map _ certificate.resources.after.loans = []; rw [certificate.closed.2]; rfl⟩

/-- A selected actual source product uses precisely the declaration environment
accepted by the full source authority checker. The result is actual numerical
checker acceptance, not merely a field equality inside a detached receipt. -/
theorem source_product_realizes {program : ResourceSource.Program} {requireMain : Bool}
    (checked : ResourceSource.Checked program requireMain)
    (entry : Nat) (found : program.entry = some entry)
    (receipt : Shapes.Functions.ProductReceipt)
    (member : receipt ∈ (checked.execution entry found).checked.context.shapes.products.toList)
    (valuation : Shapes.Valuation)
    (prior : Shapes.guardsHold valuation receipt.before.guards)
    (nominal : Shapes.guardsHold valuation (Shapes.Numerical.guards receipt.values))
    (emitted : Shapes.guardsHold valuation receipt.checked.storage.guards) :
    ∃ actual,
      Numerical.checkProduct (ResourceSource.numericalEnvironment checked.pureProgram)
        (receipt.before.eval valuation) (Shapes.Numerical.interpret valuation receipt.values)
        receipt.left receipt.right receipt.output receipt.mode receipt.policy receipt.alpha receipt.beta = .ok actual ∧
      actual.product = StorageShapeNumerical.product_eval valuation receipt.checked.product := by
  have origin := (checked.execution entry found).runtimeProductOrigins receipt member
  obtain ⟨actual, accepted, same⟩ := StorageShapeNumerical.product_realizes valuation receipt.checked prior nominal emitted
  rw [← origin]
  exact ⟨actual, accepted, same⟩

/-- Scalar return receipts include the exact runtime call slice before the
returning pure fragment. Under that call's guards, the concrete caller loans
are restored and the scalar call follows the completed resource flow. -/
theorem scalar_return_restores (receipt : Functions.ValueReturnReceipt)
    (valuation : Shapes.Valuation)
    (audited : Shapes.auditFrame receipt.runtime.call.before.resources = true)
    (prior : Shapes.guardsHold valuation receipt.runtime.call.before.resources.guards)
    (emitted : Shapes.guardsHold valuation receipt.runtime.call.guards) :
    ∃ concrete,
      Shapes.instantiate valuation 4096 receipt.runtime.call.before.resources receipt.runtime.call.slice = .ok concrete ∧
      Storage.run 4096 (receipt.runtime.call.before.resources.eval valuation) concrete =
        .ok (receipt.runtime.call.after.resources.eval valuation) ∧
      (receipt.runtime.call.after.resources.eval valuation).loans =
        (receipt.runtime.call.before.resources.eval valuation).loans ∧
      receipt.runtime.beforeFlow ++ receipt.runtime.slice ++
        [.value receipt.slot receipt.fragment receipt.arguments] = receipt.flow := by
  obtain ⟨concrete, instantiated, executed, _, restored, _⟩ :=
    StorageShapes.call_realizes valuation receipt.runtime.call audited prior emitted
  exact ⟨concrete, instantiated, executed, restored,
    by rw [receipt.runtime.prefixed]; exact receipt.emitted⟩

end VastitasOracle.ResourceRuntimeShapes
