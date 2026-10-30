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
  let some (owner, _) := program.owned[entry]? | error "missing source resource entry"
  let definition := checked.pureProgram.authority.seeds.length + entry
  let pass := checked.values.executable.lowered
  let some (_, id) := pass.origins.toList.zipIdx.find? (fun (key, _) =>
      key.definition == definition && key.targets.isEmpty)
    | error "resource return block has no executable specialization"
  let some function := checked.values.executable.core.module.functions[id]?
    | error "resource return target is absent from checked Core"
  unless function.id == id && function.definition == owner && function.parameters.isEmpty &&
      function.returnType == .pure .int do
    error "resource return target does not retain its source owner and Int signature"
  return id

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
    let target ← entryValue checked id
    let pureSource ← (Core.Codegen.generateLibrary checked.values.executable.core [target]).mapError fun message =>
      {code := "E_CODEGEN", message}
    let execution := checked.execution id entry
    let plan ← (Native.compile execution.checked.statements).mapError fun problem =>
      {code := problem.code, message := problem.message}
    let operations ← (Native.generateBody plan).mapError fun problem =>
      {code := problem.code, message := problem.message}
    let numericalImport := if plan.needsNumerical then "import VastitasGemmNative\n" else ""
    let source := "import VastitasStorageNative\n" ++ numericalImport ++ pureSource ++
      "\nopen VastitasStorageNative\n\ndef main : IO Unit := do\n" ++
      s!"  let arena ← newArena {Storage.byteLimit}\n  try\n" ++ operations ++
      s!"    IO.println ({Core.Codegen.functionReference target})\n  finally\n    close arena\n"
    return ⟨source, true, plan.needsNumerical⟩

end VastitasKernel.ResourceSource.Codegen
