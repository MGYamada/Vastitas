import VastitasKernel.ResourceSource
import VastitasKernel.IndexedCodegen

/-! The resource entry and its pure return expression belong to the same source
function. Native generation rechecks both returned components, their original
source mapping and actual dependencies. It does not run a detached sidecar. -/
namespace VastitasKernel.ResourceSource.Codegen
open Storage Indexed

private def error (message : String) : Except Diagnostic α :=
  .error {code := "E_RESOURCE_CODEGEN", message}

/-- Resolve a source resource return block through the independently audited
specialization-origin table, then verify its exact Core owner/signature again. -/
def entryValue {program : Program} (checked : Checked program true) (entry : Nat) : Except Diagnostic Nat := do
  let some function := checked.lowered.functions[entry]? | error "missing resource entry"
  let some (fragment, _, type) := function.valueResult | error "resource entry has no pure result"
  unless type == .int do error "invalid resource entry result"
  let some target := checked.targets.entries[fragment]? | error "missing checked entry fragment"
  unless target.signature.result == .int do error "resource entry must return Int"
  return target.function

private def slotName (slot : Nat) : String := s!"resourceValue_{slot}"

/-- Emit mixed operations from the exact checked Core target table. The returned
native instruction projection is compared with the independently audited raw
resource plan before any generated text is returned. -/
private def mixed (targets : List ResourcePure.Target) : Nat → Nat → Storage.State →
    List ValueFlow.Statement → Except Diagnostic (Storage.State × List Native.Instruction × String)
  | _, _, state, [] => pure (state, [], "")
  | 0, _, _, _ :: _ => error "mixed code generation exceeds traversal bound"
  | fuel + 1, indent, state, first :: rest => do
    let spaces := String.ofList (List.replicate indent ' ')
    let storage {α} (result : Except Storage.Error α) : Except Diagnostic α :=
      result.mapError fun problem => {code := problem.code, message := problem.message}
    let (after, instructions, source) ← match first with
      | .action operation => storage (Native.generateAction state operation indent)
      | .value name fragment arguments => do
        let some target := targets[fragment]? | error "missing checked pure fragment target"
        let call := Core.Codegen.functionReference target.function ++
          String.join (arguments.map fun argument => " " ++ slotName argument)
        pure (state, [], spaces ++ s!"let {slotName name} := {call}\n")
      | .branch condition yes no => do
        let (left, yesCode, yesSource) ← mixed targets fuel (indent + 2) state yes
        let (right, noCode, noSource) ← mixed targets fuel (indent + 2)
          {state with nextAllocation := left.nextAllocation} no
        let after ← storage (join left right)
        let conditionSource := match condition with
          | .literal value => toString value
          | .slot slot => slotName slot
        let source := spaces ++ s!"if {conditionSource} then\n" ++ yesSource ++ spaces ++
          "  pure ()\n" ++ spaces ++ "else\n" ++ noSource ++ spaces ++ "  pure ()\n"
        pure (after, [.branch condition.projection] ++ yesCode ++ [.skip, .otherwise] ++ noCode ++ [.skip, .finish], source)
    let (finalState, restCode, restSource) ← mixed targets fuel indent after rest
    pure (finalState, instructions ++ restCode, source ++ restSource)

structure Generated where
  source : String
  storageRuntime : Bool
  numericalRuntime : Bool

def generate (program : Program) : Except Diagnostic Generated := do
  let checked ← ResourceSource.check program true
  match entry : program.entry with
  | none =>
    let core : Core.Typing.CheckedModule true := by
      simpa [entry] using checked.pureProgram.executable.core
    let source ← (Core.Codegen.generate core).mapError fun message => {code := "E_CODEGEN", message}
    return ⟨source, false, false⟩
  | some id =>
    let _ ← entryValue checked id
    let execution := checked.execution id entry
    let _ ← (ValueFlow.check checked.targets.signatures [] execution.checked.context.flow.toList).mapError fun problem =>
      {code := problem.code, message := problem.message}
    let roots ← (ValueFlow.fragments execution.checked.context.flow.toList).mapM fun fragment =>
      match checked.targets.entries[fragment]? with
      | some target => pure target.function
      | none => error "mixed execution names an absent pure target"
    let pureSource ← (Core.Codegen.generateLibrary checked.values.executable.core roots).mapError fun message =>
      {code := "E_CODEGEN", message}
    let plan ← (Native.compile execution.checked.statements).mapError fun problem =>
      {code := problem.code, message := problem.message}
    let (finalState, instructions, operations) ← mixed checked.targets.entries 4096 4 {} execution.checked.context.flow.toList
    unless finalState == execution.checked.resources.finalState && instructions == plan.instructions do
      error "mixed emission differs from the independently checked resource plan"
    let some (result, type) := execution.checked.context.returnedValue | error "entry result slot is absent"
    unless type == .int && ValueFlow.type? execution.checked.values.finalState.slots result == some .int do
      error "entry result slot is not an available Int"
    let numericalImport := if plan.needsNumerical then "import VastitasGemmNative\n" else ""
    let source := "import VastitasStorageNative\n" ++ numericalImport ++ pureSource ++
      "\nopen VastitasStorageNative\n\ndef main : IO Unit := do\n" ++
      s!"  let arena ← newArena {Storage.byteLimit}\n  try\n" ++ operations ++
      s!"    IO.println {slotName result}\n  finally\n    close arena\n"
    return ⟨source, true, plan.needsNumerical⟩

end VastitasKernel.ResourceSource.Codegen
