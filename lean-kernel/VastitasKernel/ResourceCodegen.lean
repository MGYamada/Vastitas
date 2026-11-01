import VastitasKernel.ResourceSource
import VastitasKernel.IndexedCodegen
import VastitasKernel.StorageShapeCodegen

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
    Shapes.Native.Context → List ValueFlow.Statement →
    Except Diagnostic (Storage.State × Shapes.Native.Context × List Native.Instruction × String)
  | _, _, state, shapes, [] => pure (state, shapes, [], "")
  | 0, _, _, _, _ :: _ => error "mixed code generation exceeds traversal bound"
  | fuel + 1, indent, state, shapes, first :: rest => do
    let spaces := String.ofList (List.replicate indent ' ')
    let storage {α} (result : Except Storage.Error α) : Except Diagnostic α :=
      result.mapError fun problem => {code := problem.code, message := problem.message}
    let (after, shapeAfter, instructions, source) ← match first with
      | .action operation => do
        let (after, instructions, source) ← storage (Native.generateAction state operation indent)
        pure (after, shapes, instructions, source)
      | .runtime event => do
        let (after, source) ← storage (Shapes.Native.generate shapes event indent)
        pure (state, after, [], source)
      | .value name fragment arguments => do
        let some target := targets[fragment]? | error "missing checked pure fragment target"
        let call := Core.Codegen.functionReference target.function ++
          String.join (arguments.map fun argument => " " ++ slotName argument)
        pure (state, {shapes with slots := (name, target.signature.result) :: shapes.slots},
          [], spaces ++ s!"let {slotName name} := {call}\n")
      | .branch condition yes no => do
        if Shapes.Flow.contains yes || Shapes.Flow.contains no then
          error "runtime shapes cannot be emitted under resource branches"
        let (left, _, yesCode, yesSource) ← mixed targets fuel (indent + 2) state shapes yes
        let (right, _, noCode, noSource) ← mixed targets fuel (indent + 2)
          {state with nextAllocation := left.nextAllocation} shapes no
        let after ← storage (join left right)
        let conditionSource := match condition with
          | .literal value => toString value
          | .slot slot => slotName slot
        let source := spaces ++ s!"if {conditionSource} then\n" ++ yesSource ++ spaces ++
          "  pure ()\n" ++ spaces ++ "else\n" ++ noSource ++ spaces ++ "  pure ()\n"
        pure (after, shapes, [.branch condition.projection] ++ yesCode ++ [.skip, .otherwise] ++ noCode ++ [.skip, .finish], source)
    let (finalState, finalShapes, restCode, restSource) ← mixed targets fuel indent after shapeAfter rest
    pure (finalState, finalShapes, instructions ++ restCode, source ++ restSource)

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
    let entryTarget ← entryValue checked id
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
    let some (result, type) := execution.checked.context.returnedValue | error "entry result slot is absent"
    unless type == .int && ValueFlow.type? execution.checked.values.finalState.slots result == some .int do
      error "entry result slot is not an available Int"
    -- Inline only the last checked value call into printing. This keeps the
    -- established straight-line resource envelope while evaluating the exact
    -- entry result once, after all resource operations have completed.
    let flow := execution.checked.context.flow.toList
    let some (.value terminal fragment arguments) := flow.getLast?
      | error "entry result is not the terminal mixed operation"
    let some function := checked.lowered.functions[id]? | error "missing resource entry"
    let some (entryFragment, _, _) := function.valueResult | error "missing entry return fragment"
    let some target := checked.targets.entries[fragment]? | error "missing terminal Core target"
    unless terminal == result && fragment == entryFragment && target.function == entryTarget do
      error "terminal mixed call differs from the checked entry result"
    let hasShapes := Shapes.Flow.contains flow
    let hasStatic := !plan.instructions.isEmpty
    let indent := if hasShapes && hasStatic then 6 else 4
    let (finalState, finalShapes, instructions, operations) ← mixed checked.targets.entries 4096 indent {} {} flow.dropLast
    unless finalState == execution.checked.resources.finalState && instructions == plan.instructions do
      error "mixed emission differs from the independently checked resource plan"
    unless finalShapes.resources == execution.checked.shapes.resources.after do
      error "runtime shape emission differs from the independently checked symbolic plan"
    let resultCall := Core.Codegen.functionReference target.function ++
      String.join (arguments.map fun argument => " " ++ slotName argument)
    let shapeNumerical := execution.checked.shapes.events.any fun event =>
      match event with | .action (.gemm _) => true | _ => false
    let needsNumerical := plan.needsNumerical || shapeNumerical
    let numericalImport := if needsNumerical then "import VastitasGemmNative\n" else ""
    let envelope := if hasShapes then
      if hasStatic then
        s!"  let arena ← newArena {Storage.byteLimit}\n" ++
        Native.withUnitCleanup 2
          (s!"    let shapeArena ← newArena {Storage.byteLimit}\n" ++
            Native.withUnitCleanup 4 (operations ++ s!"      IO.println ({resultCall})\n")
              ["close shapeArena"]) ["close arena"]
      else
        s!"  let shapeArena ← newArena {Storage.byteLimit}\n" ++
        Native.withUnitCleanup 2 (operations ++ s!"    IO.println ({resultCall})\n") ["close shapeArena"]
      else
        s!"  let arena ← newArena {Storage.byteLimit}\n" ++
        Native.withUnitCleanup 2 (operations ++ s!"    IO.println ({resultCall})\n") ["close arena"]
    let source := "import VastitasStorageNative\n" ++ numericalImport ++ pureSource ++
      "\nopen VastitasStorageNative\n\ndef main : IO Unit := do\n" ++
      envelope
    return ⟨source, true, needsNumerical⟩

end VastitasKernel.ResourceSource.Codegen
